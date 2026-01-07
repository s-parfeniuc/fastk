#![warn(dead_code)]

use clap::Parser;
use concurrent_queue::ConcurrentQueue;
use core_affinity::CoreId;
use fastk::pinning_arrays;
use std::cell::UnsafeCell;
use std::collections::VecDeque;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::BufRead;
use std::io::BufReader;
use std::io::Write;
use std::path::Path;
use std::pin;
use std::ptr;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
use std::sync::{atomic::AtomicBool, Arc, Barrier};
use std::thread;
use std::time::Instant;
use std::u16;

#[inline(always)]
fn neighbors_slice<'a>(offsets: &'a [u32], neighbors: &'a [u32], v: usize) -> &'a [u32] {
    let start = offsets[v];
    let end = offsets[v + 1];
    &neighbors[start as usize..end as usize]
}

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Questo modulo richiede un usize a 64 bit (target_pointer_width = 64).");

pub mod estab {

    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    pub const SHIFT: usize = 32;

    // estimate: 31 bit value + 1 bit spec flag (MSB of low 32)
    pub const EST_FLAG_MASK: usize = 0x8000_0000; // MSB of low dword
    pub const EST_VALUE_MASK: usize = 0x7FFF_FFFF; // lower 31 bits for estimate value
    pub const EST_FIELD_MASK: usize = 0xFFFF_FFFF; // whole low dword (flag + value)
    pub const STAB_MASK: usize = 0xFFFF_FFFF_0000_0000; // high dword

    // ---------- pack/unpack con stability con segno (i32) ----------
    #[inline(always)]
    pub const fn pack(stability_i32: i32, estimate_raw: u32, spec_enabled: bool) -> usize {
        let mut low = (estimate_raw as usize) & EST_VALUE_MASK;
        if spec_enabled {
            low |= EST_FLAG_MASK;
        }
        (((stability_i32 as u32) as usize) << SHIFT) | (low as usize)
    }

    /// Restituisce la stima numerica reale (senza il bit flag).
    #[inline(always)]
    pub const fn estimate(x: usize) -> u32 {
        (x & EST_VALUE_MASK) as u32
    }

    /// Restituisce true se la speculazione è abilitata (MSB del low dword).
    #[inline(always)]
    pub const fn is_spec_enabled(x: usize) -> bool {
        (x & EST_FLAG_MASK) != 0
    }

    /// Restituisce la stability come i32 (sign-extend 32bit).
    #[inline(always)]
    pub const fn stability(x: usize) -> i32 {
        // sign-extend dei 32 bit alti
        ((x >> SHIFT) as u32) as i32
    }

    /// Imposta il campo estimate (lascia intatta la flag spec).
    #[inline(always)]
    pub const fn set_estimate(x: usize, est_raw: u32) -> usize {
        let flag = x & EST_FLAG_MASK;
        (x & STAB_MASK) | (flag) | ((est_raw as usize) & EST_VALUE_MASK)
    }

    /// Imposta la flag spec_enabled (lascia intatto value e stability).
    #[inline(always)]
    pub const fn set_spec_enabled(x: usize, enabled: bool) -> usize {
        if enabled {
            x | EST_FLAG_MASK
        } else {
            x & !EST_FLAG_MASK
        }
    }

    /// Imposta la stability (lascia intatto il low dword).
    #[inline(always)]
    pub const fn set_stability(x: usize, stab_i32: i32) -> usize {
        (x & EST_FIELD_MASK) | (((stab_i32 as u32) as usize) << SHIFT)
    }

    // ---------- helper per debug / packing completo ----------
    #[inline(always)]
    pub const fn estimate_with_flag(x: usize) -> u32 {
        (x & EST_FIELD_MASK) as u32
    }

    /// Decrementa stability di 'delta' se estimate è compresa tra old_est (escluso) e new_est (incluso).
    /// Restituisce Some((prev_word, crossed)) se l'aggiornamento è avvenuto, None altrimenti.
    /// crossed è true se si è passati da stability non negativa a negativa.
    #[inline(always)]
    pub fn fetch_update_stability(
        a: &AtomicUsize,
        delta: i32,
        old_est: u32,
        new_est: u32,
    ) -> Option<(usize, bool)> {
        // closure atomica che modifica stab e, se condizione verificata e flag settata, applica
        // anche il decremento speculativo su estimate (saturating_sub).
        match a.fetch_update(Ordering::SeqCst, Ordering::Relaxed, |cur| {
            let est = self::estimate(cur);
            let spec = self::is_spec_enabled(cur);
            let s = self::stability(cur);

            // la condizione originale: new_est < est && est as i32 + s.min(0) <= old_est as i32
            if new_est < est && (est as i32 + s.min(0)) <= old_est as i32 {
                // calcolo nuovo stability
                let new_stab = s.wrapping_sub(delta);
                // Se lo stab passa da 0 a -1 e spec è abilitata, applico decremento speculativo all'estimate.
                let new_est_val = est;
                Some(self::pack(new_stab, new_est_val, spec))
            } else {
                None
            }
        }) {
            Ok(prev) => {
                let old_stab = self::stability(prev);
                let new_stab = old_stab - delta;
                let crossed = old_stab >= 0 && new_stab < 0;
                Some((prev, crossed))
            }
            Err(_) => None,
        }
    }

    /// Aggiorna estimate a new_est e stability a curr_stab + (new_stab - old_stab).
    /// Restituisce true se la nuova stability è non negativa. Altrimenti restituisce false.
    #[inline(always)]
    pub fn publish_estab(a: &AtomicUsize, new_est: u32, old_stab: i32, new_stab: i32) -> bool {
        let delta = new_stab - old_stab;
        // prima applico la publish atomica (come prima)
        let result = a
            .fetch_update(Ordering::SeqCst, Ordering::Relaxed, |cur| {
                let current_stab = self::stability(cur);
                let next_stab = current_stab + delta;
                let spec_enabled = current_stab == old_stab;
                Some(self::pack(next_stab, new_est, spec_enabled))
            })
            .expect("error in publish_estab");

        // infine il controllo di coerenza originale (se la nuova stability è negativa, bisogna ricalcolare)
        if stability(result) + delta < 0 {
            return false;
        }
        true
    }

    /// Restituisce l'old_est usato nel ricalcolo: se stability < 0 e spec_enabled è true,
    /// allora la stima corrente è stata speculativamente decrementata e l'old_est = est + 1.
    #[inline(always)]
    pub const fn old_est_from_word(x: usize) -> u32 {
        let est = estimate(x);
        let spec = is_spec_enabled(x);
        let stab = stability(x);
        if stab < 0 && spec {
            est.saturating_add(1)
        } else {
            est
        }
    }
}

#[derive(Clone, Copy)]
pub struct State {
    last_update: u16,
    in_queue: bool,
}

pub struct InfoStore {
    estimate_stability: Box<[AtomicUsize]>,
    info: UnsafeCell<Box<[(State, u32)]>>,
    num_nodes: usize,
}

impl InfoStore {
    fn new(num_nodes: usize) -> Self {
        let estimate_stability = (0..num_nodes)
            .map(|_| AtomicUsize::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let info = (0..num_nodes)
            .map(|_| {
                (
                    State {
                        last_update: 0,
                        in_queue: false,
                    },
                    0,
                )
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();

        InfoStore {
            estimate_stability,
            info: UnsafeCell::new(info),
            num_nodes,
        }
    }
    #[inline(always)]
    pub fn load_estab(&self, id: usize, ordering: Ordering) -> usize {
        self.estimate_stability[id].load(ordering)
    }

    #[inline(always)]
    pub fn store_estab(&self, id: usize, (estimate, stability): (u32, i32)) {
        self.estimate_stability[id]
            .store(estab::pack(stability, estimate, false), Ordering::Relaxed);
    }

    /// Aggiorna estimate a new_est e stability a curr_stab + (new_stab - old_stab).
    /// Restituisce true se la nuova stability è non negativa. Altrimenti restituisce false, che
    /// significa che la stima appena calcolata non è più affidabile e va ricalcolata.
    #[inline(always)]
    pub fn publish_estab(&self, id: usize, new_est: u32, old_stab: i32, new_stab: i32) -> bool {
        estab::publish_estab(&self.estimate_stability[id], new_est, old_stab, new_stab)
    }

    /// Decrementa stability di 'delta' se estimate è compresa tra old_est (escluso) e new_est (incluso).
    /// Restituisce Some((new_stab, crossed)) se l'aggiornamento è avvenuto, None altrimenti. crossed è true se si è passati da stability non negativa a negativa.
    #[inline(always)]
    pub fn fetch_update_stability(
        &self,
        id: usize,
        delta: i32,
        old_est: u32,
        new_est: u32,
    ) -> Option<(usize, bool)> {
        estab::fetch_update_stability(&self.estimate_stability[id], delta, old_est, new_est)
    }

    #[inline(always)]
    pub unsafe fn info_cell_mut(&self, id: usize) -> *mut (State, u32) {
        // otteniamo &mut Box<[(State,u32)]> da UnsafeCell
        let p_box: *mut Box<[(State, u32)]> = self.info.get();
        // puntatore base all'array
        let base: *mut (State, u32) = (*p_box).as_mut_ptr();
        base.add(id)
    }

    /// restituise l'informazione associata al nodo `id`
    #[inline(always)]
    pub fn get_info(&self, id: usize) -> (State, u32) {
        unsafe { *self.info_cell_mut(id) }
    }

    #[inline(always)]
    pub fn set_in_queue(&self, id: usize, val: bool) {
        unsafe {
            (*self.info_cell_mut(id)).0.in_queue = val;
        }
    }

    #[inline(always)]
    pub fn set_degree(&self, id: usize, deg: u32) {
        unsafe {
            (*self.info_cell_mut(id)).1 = deg;
        }
    }

    #[inline(always)]
    pub fn set_last_update(&self, id: usize, iter: u16) {
        unsafe {
            (*self.info_cell_mut(id)).0.last_update = iter;
        }
    }

    #[inline(always)]
    pub fn get_last_update(&self, id: usize) -> u16 {
        unsafe { (*self.info_cell_mut(id)).0.last_update }
    }

    #[inline(always)]
    pub fn get_degree(&self, id: usize) -> u32 {
        unsafe { (*self.info_cell_mut(id)).1 }
    }

    /// Chiamato quando il nodo viene inserito in coda.
    /// Restituisce true se il nodo deve essere effettivamente inserito in coda,
    /// false se era già in coda o se è già stato aggiornato in questa iterazione.
    #[inline(always)]
    pub fn try_enqueue(&self, id: usize, iteration: usize) -> bool {
        unsafe {
            let p = self.info_cell_mut(id);
            let st = &mut (*p).0;
            if st.in_queue || st.last_update == iteration as u16 {
                return false;
            }
            st.in_queue = true;
        }
        true
    }

    /// Restituisce il grado del nodo `id`.
    pub fn degree_of(&self, id: usize) -> u32 {
        unsafe { (*self.info_cell_mut(id)).1 }
    }

    /// Chiamato quando il nodo viene estratto dalla coda.
    /// Setta in_queue a false e last_update a iteration
    #[inline(always)]
    pub fn dequeue(&self, id: usize, iteration: usize) {
        unsafe {
            let p = self.info_cell_mut(id);
            (*p).0.in_queue = false;
            (*p).0.last_update = iteration as u16;
        }
    }

    /// Decrementa stability di 'id' di 'offset', restituisce true se la stability è diventata negativa
    #[inline(always)]
    pub fn update_stability(&self, id: usize, offset: i32) -> bool {
        let prev = self.estimate_stability[id]
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |cur| {
                let s = estab::stability(cur);
                let ns = s.wrapping_sub(offset);
                Some(estab::set_stability(cur, ns))
            })
            .expect("fatal error update_stability");
        if estab::stability(prev) < offset {
            return true;
        }
        return false;
    }
}

unsafe impl Send for InfoStore {}
unsafe impl Sync for InfoStore {}

#[derive(Copy, Clone, Debug)]
pub struct BatchBudget {
    pub min_nodes: usize, // soglia di chiusura
    pub max_nodes: usize, // limite duro
    pub max_edges: usize, // limite duro (attivo se len >= min_nodes)
}

pub struct DualLocalPQ {
    queues: [LocalPQ; 2],
    cur: usize,
}

impl DualLocalPQ {
    pub fn new(
        mapper: ExpoSubBuckets,
        shared_pq: Arc<SharedPQ>,
        budget: BatchBudget,
        vgc_enabled: bool,
        vgc_threshold: usize,
    ) -> Self {
        Self {
            queues: [
                LocalPQ::new(
                    mapper,
                    Arc::clone(&shared_pq),
                    budget,
                    vgc_enabled,
                    vgc_threshold,
                ),
                LocalPQ::new(mapper, Arc::clone(&shared_pq), budget, false, vgc_threshold),
            ],
            cur: 0,
        }
    }

    #[inline]
    pub fn current_mut(&mut self) -> &mut LocalPQ {
        &mut self.queues[self.cur]
    }

    #[inline]
    pub fn next_mut(&mut self) -> &mut LocalPQ {
        &mut self.queues[self.cur ^ 1]
    }

    /// Scambia current e next (da chiamare a fine **iterazione**, non di sottoiterazione).
    #[inline]
    pub fn flip(&mut self) {
        self.queues[self.cur ^ 1].vgc_enabled = self.queues[self.cur].vgc_enabled;
        self.queues[self.cur].vgc_enabled = false;
        self.cur ^= 1;
    }

    /// Inserisce un nodo in current o next a seconda di last_update.
    /// Se last_update == iteration, inserisce in next, altrimenti in current.
    #[inline]
    pub fn push_node(
        &mut self,
        level: usize,
        old_prio: usize,
        node: usize,
        edges: usize,
        last_update: u16,
        iteration: u16,
    ) {
        if last_update == iteration {
            self.next_mut().push_node(level, old_prio, node, edges);
        } else {
            self.current_mut().push_node(level, old_prio, node, edges);
        }
    }
}

pub struct LocalPQ {
    pq: Vec<Option<Batch>>,
    mapper: ExpoSubBuckets,
    bitmap: BitHierarchy,
    shared_pq: Arc<SharedPQ>,
    vgc_enabled: bool,
    vgc_threshold: usize,
    vgc_current: usize,
    budget: BatchBudget,
    closed_batches: Vec<(usize, Batch)>,
    current_batch: Batch,
    edges: usize,
}

impl LocalPQ {
    pub fn new(
        mapper: ExpoSubBuckets,
        shared_pq: Arc<SharedPQ>,
        budget: BatchBudget,
        vgc_enabled: bool,
        vgc_threshold: usize,
    ) -> Self {
        let max_buckets = mapper.total_buckets();
        Self {
            pq: vec![None; max_buckets],
            mapper,
            bitmap: BitHierarchy::new(max_buckets),
            shared_pq,
            vgc_enabled,
            vgc_threshold: vgc_threshold,
            vgc_current: 0,
            closed_batches: Vec::new(),
            budget,
            current_batch: Batch {
                prio: 0,
                edges: 0,
                nodes: VecDeque::with_capacity(budget.max_nodes),
            },
            edges: 0,
        }
    }
    pub fn flush(&mut self, cutoff: usize) {
        for (level, batch) in self.closed_batches.drain(..) {
            self.shared_pq.push_batch(level, batch);
        }
        for (level, batch) in self.pq.iter_mut().enumerate() {
            self.bitmap.clear_bucket(level);
            if level > cutoff {
                break;
            }
            if batch.is_some() {
                self.shared_pq.push_batch(level, batch.take().unwrap());
            }
        }
        self.vgc_current = 0;
    }

    pub fn flush_optimized(&mut self, cutoff: usize) {
        for (level, batch) in self.closed_batches.drain(..) {
            self.shared_pq.push_batch(level, batch);
        }
        while let Some(level) = self.bitmap.first_set_at_most(cutoff) {
            if let Some(batch) = self.pq[level].take() {
                self.shared_pq.push_batch(level, batch);
            }
            self.bitmap.clear_bucket(level);
        }
        self.vgc_current = 0;
    }

    #[inline]
    pub fn pop_first(&mut self, prio: usize) -> Option<usize> {
        // controllo se ci sono nodi nell'open batch, altrimenti provo a prenderne uno dalla shared pq
        if let Some(node) = self.current_batch.nodes.pop_front() {
            return Some(node);
        } else {
            if let Some(level) = self.bitmap.first_set_at_most(prio) {
                self.current_batch = self.pq[level].take().unwrap();
                self.edges += self.current_batch.edges;
                self.bitmap.clear_bucket(level);
            } else {
                self.current_batch = self.shared_pq.pop_batch(prio)?;
            }
        }
        self.current_batch.nodes.pop_front()
    }

    #[inline]
    pub fn pop_node(&mut self, prio: usize) -> Option<usize> {
        // controllo se ci sono nodi nell'open batch, altrimenti provo a prenderne uno dalla shared pq
        if let Some(node) = self.current_batch.nodes.pop_front() {
            return Some(node);
        } else {
            self.current_batch = self.shared_pq.pop_batch(prio)?;
        }
        self.current_batch.nodes.pop_front()
    }

    pub fn push_node(&mut self, prio: usize, old_prio: usize, node: usize, edges: usize) {
        // inserisco direttamente nel current batch se VGC attivo e soglia non superata
        if self.vgc_enabled && self.vgc_current < self.vgc_threshold && prio < old_prio {
            self.current_batch.nodes.push_front(node);
            self.vgc_current += 1;
            self.edges += edges;
            return;
        }
        let bucket = self.mapper.map(prio);
        self.bitmap.set_bucket(bucket);
        if self.pq[bucket].is_none() {
            let mut nodes = VecDeque::with_capacity(128);
            nodes.push_back(node);
            self.pq[bucket] = Some(Batch {
                prio: bucket,
                edges: edges,
                nodes,
            });
        } else {
            let open_batch = self.pq[bucket].as_mut().unwrap();
            open_batch.push_node(node, edges);
            if open_batch.should_close(&self.budget) {
                self.closed_batches
                    .push((bucket, self.pq[bucket].take().unwrap()));
            }

            self.bitmap.clear_bucket(bucket);
        }
    }
}

#[inline]
fn ilog2_usize(x: usize) -> usize {
    debug_assert!(x > 0);
    (usize::BITS as usize - 1) - x.leading_zeros() as usize
}

// ===================== MAPPER =====================
#[derive(Debug, Clone, Copy)]
pub struct ExpoSubBuckets {
    base_exact: usize,
    sub_buckets: usize,
    max_level: usize,
    base_log2: usize,
    total_buckets: usize,
}

impl ExpoSubBuckets {
    pub fn new(max_level: usize, base_exact: usize, sub_buckets: usize) -> Self {
        assert!(base_exact >= 1 && sub_buckets >= 1);
        let base_log2 = ilog2_usize(base_exact.next_power_of_two());

        let mut bands_full = 0usize;
        if max_level >= base_exact {
            let mut k = 0usize;
            loop {
                let band_start = base_exact.checked_shl(k as u32).unwrap_or(usize::MAX);
                let band_end_inclusive = base_exact
                    .checked_shl((k as u32) + 1)
                    .unwrap_or(usize::MAX)
                    .saturating_sub(1);
                if band_start > max_level {
                    break;
                }
                if band_end_inclusive <= max_level {
                    bands_full += 1;
                    k += 1;
                    continue;
                }
                break;
            }
        }

        let exact_buckets = (max_level + 1).min(base_exact);
        let full_band_buckets = if max_level >= base_exact {
            bands_full * sub_buckets
        } else {
            0
        };

        let mut partial_band_buckets = 0usize;
        if max_level >= base_exact {
            let k = bands_full;
            let band_start = base_exact.checked_shl(k as u32).unwrap_or(usize::MAX);
            if band_start <= max_level {
                assert!(
                    (base_exact << k) % sub_buckets == 0,
                    "Richiesto: (base_exact << k) % sub_buckets == 0"
                );
                let step = (base_exact << k) / sub_buckets;
                let covered = max_level.saturating_sub(band_start).saturating_add(1);
                partial_band_buckets = (covered + step - 1) / step;
                if partial_band_buckets > sub_buckets {
                    partial_band_buckets = sub_buckets;
                }
            }
        }

        let total_buckets = exact_buckets + full_band_buckets + partial_band_buckets;
        Self {
            base_exact,
            sub_buckets,
            max_level,
            base_log2,
            total_buckets,
        }
    }

    #[inline]
    pub fn total_buckets(&self) -> usize {
        self.total_buckets
    }

    #[inline]
    pub fn map(&self, mut level: usize) -> usize {
        if level > self.max_level {
            level = self.max_level;
        }
        if level < self.base_exact {
            return level;
        }
        let k = ilog2_usize(level) - self.base_log2;
        let band_base_bucket = self.base_exact + k * self.sub_buckets;
        let band_start = self.base_exact << k;
        let step = (self.base_exact << k) / self.sub_buckets;
        let offset = level - band_start;
        let sub = (offset / step).min(self.sub_buckets - 1);
        band_base_bucket + sub
    }

    #[allow(dead_code)]
    pub fn bucket_span(&self, bucket: usize) -> (usize, usize) {
        assert!(bucket < self.total_buckets);
        if bucket < self.base_exact {
            return (bucket, bucket);
        }
        let rel = bucket - self.base_exact;
        let k = rel / self.sub_buckets;
        let sub = rel % self.sub_buckets;
        let band_start = self.base_exact << k;
        let step = (self.base_exact << k) / self.sub_buckets;
        let lo = band_start + sub * step;
        let hi = lo + step - 1;
        (lo.min(self.max_level), hi.min(self.max_level))
    }
}

// ===================== DATI E PQ =====================
#[derive(Debug, Clone)]
pub struct Batch {
    pub prio: usize,
    pub edges: usize,
    pub nodes: VecDeque<usize>,
}

impl Batch {
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    #[inline]
    pub fn push_node(&mut self, node: usize, edges: usize) {
        self.nodes.push_back(node);
        self.edges += edges;
    }

    #[inline]
    pub fn should_close(&self, budget: &BatchBudget) -> bool {
        if self.len() >= budget.max_nodes {
            return true;
        }
        if self.len() >= budget.min_nodes && self.edges >= budget.max_edges {
            return true;
        }
        false
    }
}

struct BucketMeta {
    queue: AtomicPtr<ConcurrentQueue<Batch>>,
    count: AtomicUsize,
}
impl BucketMeta {
    fn new() -> Self {
        Self {
            queue: AtomicPtr::new(std::ptr::null_mut()),
            count: AtomicUsize::new(0),
        }
    }
    #[inline]
    fn queue_or_init(&self) -> &ConcurrentQueue<Batch> {
        let mut p = self.queue.load(Ordering::Relaxed);
        if p.is_null() {
            let boxed = Box::new(ConcurrentQueue::<Batch>::unbounded());
            let raw = Box::into_raw(boxed);
            match self.queue.compare_exchange(
                ptr::null_mut(),
                raw,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => p = raw,
                Err(existing) => unsafe {
                    drop(Box::from_raw(raw));
                    p = existing;
                },
            }
        }
        unsafe { &*p }
    }
}

struct BitHierarchy {
    level_bits: Vec<Vec<AtomicUsize>>, // usare usize per or/and 64-bit portable
}
impl BitHierarchy {
    fn new(n_buckets: usize) -> Self {
        assert!(n_buckets > 0);
        let mut level_bits: Vec<Vec<AtomicUsize>> = Vec::new();
        let mut words = (n_buckets + 63) / 64;
        let mut v = Vec::new();
        for _ in 0..words {
            v.push(AtomicUsize::new(0));
        }
        level_bits.push(v);
        while words > 1 {
            words = (words + 63) / 64;
            let mut v = Vec::new();
            for _ in 0..words {
                v.push(AtomicUsize::new(0));
            }
            level_bits.push(v);
        }
        Self { level_bits }
    }
    #[inline]
    fn levels(&self) -> usize {
        self.level_bits.len()
    }
    #[inline]
    fn set_bucket(&self, idx: usize) {
        let mut word_idx = idx >> 6;
        let bit = 1usize << (idx & 63);
        let _prev = self.level_bits[0][word_idx].fetch_or(bit, Ordering::Relaxed);
        for lvl in 1..self.levels() {
            let upper_bit = 1usize << (word_idx & 63);
            word_idx >>= 6;
            self.level_bits[lvl][word_idx].fetch_or(upper_bit, Ordering::Relaxed);
        }
    }
    #[inline]
    fn clear_bucket(&self, idx: usize) {
        let mut word_idx = idx >> 6;
        let bit = 1usize << (idx & 63);
        let new_word = self.level_bits[0][word_idx].fetch_and(!bit, Ordering::Relaxed) & !bit;
        if new_word == 0 {
            for lvl in 1..self.levels() {
                let upper_bit = 1usize << (word_idx & 63);
                word_idx >>= 6;
                let new_upper = self.level_bits[lvl][word_idx]
                    .fetch_and(!upper_bit, Ordering::Relaxed)
                    & !upper_bit;
                if new_upper != 0 {
                    break;
                }
            }
        }
    }

    #[inline]
    fn first_set_at_most(&self, cutoff: usize) -> Option<usize> {
        let mut limit_word_idx = cutoff >> 6;
        let top = self.levels() - 1;
        let mut chosen = vec![0usize; self.levels()];
        for lvl in (0..=top).rev() {
            let words = &self.level_bits[lvl];
            if words.is_empty() {
                return None;
            }
            let max_w = words.len().saturating_sub(1);
            let lim = limit_word_idx.min(max_w);
            let mut found = None;
            for wi in 0..=lim {
                let w = words[wi].load(Ordering::Relaxed);
                if w != 0 {
                    let b = w.trailing_zeros() as usize;
                    chosen[lvl] = (wi << 6) | b;
                    found = Some(());
                    break;
                }
            }
            if found.is_none() {
                return None;
            }
            limit_word_idx = chosen[lvl];
        }
        let leaf_word_idx = chosen[0] >> 6;
        let bit_in_word = chosen[0] & 63;
        let idx = (leaf_word_idx << 6) | bit_in_word;
        (idx <= cutoff).then_some(idx)
    }
}

pub struct SharedPQ {
    n_buckets: usize,
    buckets: Vec<BucketMeta>,
    bits: BitHierarchy,
    block_counts: Vec<AtomicUsize>,
}
impl SharedPQ {
    pub fn new(n_buckets: usize) -> Self {
        assert!(n_buckets > 0);
        let buckets = (0..n_buckets).map(|_| BucketMeta::new()).collect();
        let bits = BitHierarchy::new(n_buckets);
        let mut vector = Vec::new();
        for _ in 0..(n_buckets + 63) / 64 {
            vector.push(AtomicUsize::new(0));
        }
        let block_counts = vector;
        Self {
            n_buckets,
            buckets,
            bits,
            block_counts,
        }
    }
    #[inline]
    pub fn push_batch(&self, level: usize, batch: Batch) {
        debug_assert!(level < self.n_buckets);
        let q = self.buckets[level].queue_or_init();
        q.push(batch).expect("unbounded queue push");
        let old = self.buckets[level].count.fetch_add(1, Ordering::Relaxed);
        let block_idx = level >> 6;
        self.block_counts[block_idx].fetch_add(1, Ordering::Relaxed);
        let _ = old;
        self.bits.set_bucket(level);
    }
    #[inline]
    pub fn pop_batch(&self, cutoff: usize) -> Option<Batch> {
        if cutoff >= self.n_buckets {
            return None;
        }
        let idx = self.bits.first_set_at_most(cutoff)?;
        let q = self.buckets[idx].queue_or_init();
        if let Ok(batch) = q.pop() {
            let prev = self.buckets[idx].count.fetch_sub(1, Ordering::Relaxed);
            debug_assert!(prev > 0);
            let block_idx = idx >> 6;
            self.block_counts[block_idx].fetch_sub(1, Ordering::Relaxed);
            if prev == 1 {
                self.bits.clear_bucket(idx);
            }
            Some(batch)
        } else {
            if self.buckets[idx].count.load(Ordering::Relaxed) == 0 {
                self.bits.clear_bucket(idx);
            }
            None
        }
    }
    pub fn approx_len(&self) -> usize {
        self.block_counts
            .iter()
            .map(|c| c.load(Ordering::Relaxed))
            .sum()
    }

    pub fn estimate_cutoff(&self, target_batches_per_subiter: usize) -> Option<usize> {
        if target_batches_per_subiter == 0 {
            // caso degenere: il primo bucket non vuoto, altrimenti 0
            if let Some(idx) = self
                .bits
                .first_set_at_most(self.n_buckets.saturating_sub(1))
            {
                return Some(idx);
            }
            if self.approx_len() > 0 {
                println!("Incoerenza: bitarray vuota ma contatori non nulli");
            }
            return None;
        }

        let n_blocks = self.block_counts.len();
        let mut total = 0usize;
        let mut block = 0usize;

        // 1) avanza a blocchi finché superi (o raggiungi) il target
        while block < n_blocks {
            let c = self.block_counts[block].load(Ordering::Relaxed);
            if c == 0 {
                block += 1;
                continue;
            }
            if total + c >= target_batches_per_subiter {
                // 2) blocco critico: raffina nei 64 bucket del blocco
                let start_idx = block << 6;
                let end_idx = ((block + 1) << 6).min(self.n_buckets);

                // somma progressiva fino a raggiungere/superare il target
                for idx in start_idx..end_idx {
                    let ci = self.buckets[idx].count.load(Ordering::Relaxed);
                    if ci == 0 {
                        continue;
                    }
                    total += ci;
                    if total >= target_batches_per_subiter {
                        return Some(idx);
                    }
                }

                // Non abbiamo raggiunto il target all'interno del blocco:
                // ritorna l’ultimo bucket non vuoto nel blocco (best-effort coerente).
                for idx in (start_idx..end_idx).rev() {
                    if self.buckets[idx].count.load(Ordering::Relaxed) > 0 {
                        return Some(idx);
                    }
                }
                // Se il blocco risulta vuoto (contatore impreciso), continua coi blocchi successivi
                block += 1;
                continue;
            } else {
                total += c;
                block += 1;
            }
        }

        // 3) Non c’è abbastanza lavoro per il target:
        // ritorna l’ultimo bucket non vuoto globale, o n_buckets-1 se tutto vuoto.
        for idx in (0..self.n_buckets).rev() {
            if self.buckets[idx].count.load(Ordering::Relaxed) > 0 {
                return Some(idx);
            }
        }
        if self.approx_len() > 0 {
            println!("Incoerenza: bitarray vuota ma contatori non nulli");
        }
        None
    }
}
impl Drop for SharedPQ {
    fn drop(&mut self) {
        for b in &self.buckets {
            let p = b.queue.load(Ordering::Relaxed);
            if !p.is_null() {
                unsafe {
                    drop(Box::from_raw(p));
                }
            }
        }
    }
}

pub struct Graph {
    pub num_nodes: u32,
    pub offsets: Vec<u32>,
    pub neighbors: Vec<u32>,
    pub avg_deg: u32,
    pub max_deg: u32,
    pub name: String,
}

impl Graph {
    pub fn parse_file(path: &str, pinning: &[usize; 128]) -> Self {
        let file = BufReader::new(File::open(path).expect("File inesistente"));
        if pinning[0] != usize::MAX {
            pin_thread_strict(0, pinning);
        }

        let mut edges: Vec<(u32, u32)> = vec![];
        let mut max_node = 0;

        for line in file.lines() {
            let line = line.unwrap();
            if line.starts_with('#') || line.trim().is_empty() || line.starts_with('%') {
                continue;
            }
            let mut parts = line.split_whitespace();
            let u: u32 = parts.next().unwrap().parse().unwrap();
            let v: u32 = parts.next().unwrap().parse().unwrap();
            if parts.next().is_some() {
                continue;
            }
            max_node = max_node.max(u).max(v);
            if u < v {
                edges.push((u, v));
                edges.push((v, u));
            }
        }

        let num_nodes = max_node + 1;
        let mut degree = vec![0; num_nodes as usize];
        for &(u, _) in &edges {
            degree[u as usize] += 1;
        }

        let mut offsets: Vec<u32> = vec![0; num_nodes as usize + 1];
        let mut max_deg = 0;
        for i in 0..num_nodes {
            offsets[i as usize + 1] = offsets[i as usize] + degree[i as usize];
            max_deg = max_deg.max(degree[i as usize]);
        }

        let mut neighbors = vec![0; offsets[num_nodes as usize] as usize];
        let mut fill = vec![0; num_nodes as usize];
        for i in 0..num_nodes {
            fill[i as usize] = offsets[i as usize];
        }

        for &(u, v) in &edges {
            neighbors[fill[u as usize] as usize] = v;
            fill[u as usize] += 1;
        }

        // per il nome del grafo, prendo solo il nome dell'ultima directory, senza il nome del file e senza il path
        let path_obj = Path::new(path);
        let file_stem = path_obj
            .ancestors()
            .nth(1)
            .and_then(|p| p.file_name())
            .and_then(|s| s.to_str())
            .unwrap_or("graph");
        Graph {
            num_nodes,
            offsets,
            neighbors,
            max_deg: max_deg,
            avg_deg: edges.len() as u32 / num_nodes as u32,
            name: file_stem.to_string(),
        }
    }

    #[inline(always)]
    pub fn neighbors_of(&self, u: usize) -> &[u32] {
        let (s, e) = (self.offsets[u], self.offsets[u + 1]);
        &self.neighbors[s as usize..e as usize]
    }

    #[inline(always)]
    pub fn degree_of(&self, u: usize) -> u32 {
        self.offsets[u + 1] - self.offsets[u]
    }

    pub fn fastk(
        &self,
        num_threads: usize,
        chunk_size: usize,
        vgc_enabled: bool,
        vgc_threshold: usize,
        out_file: &str,
        target_batches_per_subiter: usize,
        pinning: &[usize; 128],
        alg_name: &str,
    ) {
        pin_thread_strict(0, pinning);
        let batch_budget = BatchBudget {
            min_nodes: 1,
            max_nodes: chunk_size, // cardinalità massima per batch
            max_edges: self.avg_deg as usize * chunk_size, // budget in archi per batch
        };

        let mapper = ExpoSubBuckets::new(self.max_deg as usize, 512, 64);

        let shared_pq = Arc::new(SharedPQ::new(mapper.total_buckets()));

        // Barriera condivisa
        let phase_barrier = Arc::new(Barrier::new(num_threads));

        // Controllo coordinatore/worker
        let end_iteration = Arc::new(AtomicBool::new(false));
        let terminate = Arc::new(AtomicBool::new(false));
        let current_priority = Arc::new(AtomicUsize::new(2));

        let nodes: &[u32] = &self.offsets;
        let edges: &[u32] = &self.neighbors;

        let threads_working = Arc::new(AtomicUsize::new(num_threads));

        let edges_processed = Arc::new(AtomicUsize::new(0));

        let info = Arc::new(InfoStore::new(self.num_nodes as usize));

        thread::scope(|scope| {
            for tid in 0..num_threads {
                let info = Arc::clone(&info);
                let phase_barrier = Arc::clone(&phase_barrier);
                let offsets = nodes;
                let neighbors = edges;
                let end_iteration = Arc::clone(&end_iteration);
                let terminate = Arc::clone(&terminate);
                let current_priority = Arc::clone(&current_priority);
                let threads_working = Arc::clone(&threads_working);
                let edges_processed = Arc::clone(&edges_processed);
                let shared_pq = Arc::clone(&shared_pq);

                scope.spawn(move || {
                    thread_routine(
                        tid,
                        info,
                        shared_pq,
                        phase_barrier,
                        offsets,
                        neighbors,
                        end_iteration,
                        terminate,
                        current_priority,
                        batch_budget,
                        threads_working,
                        edges_processed,
                        num_threads,
                        mapper,
                        vgc_enabled,
                        vgc_threshold,
                        out_file.to_string().clone(),
                        self.name.clone(),
                        target_batches_per_subiter,
                        &pinning,
                        alg_name,
                    )
                });
            }
        });
    }
}

#[inline(always)]
pub fn thread_routine(
    tid: usize,
    info: Arc<InfoStore>,
    shared_pq: Arc<SharedPQ>,
    phase_barrier: Arc<Barrier>,
    offsets: &[u32],
    neighbors: &[u32],
    end_iteration: Arc<AtomicBool>,
    terminate: Arc<AtomicBool>,
    current_priority: Arc<AtomicUsize>,
    batch_budget: BatchBudget,
    threads_working: Arc<AtomicUsize>,
    edges_processed: Arc<AtomicUsize>,
    num_threads: usize,
    mapper: ExpoSubBuckets,
    vgc_enabled: bool,
    vgc_threshold: usize,
    out_file: String,
    graph_name: String,
    target_batches_per_subiter: usize,
    pinning: &[usize; 128],
    alg_name: &str,
) {
    //=================================================================

    // Pinning..
    if pinning[tid] != usize::MAX {
        pin_thread_strict(tid, pinning);
    }

    let target_batches_per_subiteration = num_threads * target_batches_per_subiter;

    // prefilling disgiunto per owner: nessuna barriera necessaria
    // ogni thread si prende una parte in base al proprio tid

    let mut local_queues: DualLocalPQ = DualLocalPQ::new(
        mapper,
        Arc::clone(&shared_pq),
        batch_budget,
        vgc_enabled,
        vgc_threshold,
    );
    local_queues.current_mut().vgc_current = vgc_threshold;

    let n = info.num_nodes;
    let chunk = (n + num_threads - 1) / num_threads;
    let start = tid * chunk;
    let end = (start + chunk).min(n);
    let start_t = Instant::now();

    for u in start..end {
        let deg = (offsets[u + 1] - offsets[u]) as u32;
        // inizializzo estimate e stability
        info.store_estab(u, (deg, -(2 * deg as i32)));

        info.set_degree(u, deg);
        if deg > 1 {
            info.set_in_queue(u, true);
            info.set_last_update(u, 0);
            local_queues
                .current_mut()
                .push_node(deg as usize, 0, u, info.degree_of(u) as usize);
        }
    }
    local_queues.current_mut().flush(usize::MAX);

    // Fine prefilling
    phase_barrier.wait();
    //================================================
    // Inizio iterazioni
    //================================================

    let mut count = Vec::new();
    let mut temp = Vec::new();

    let mut subiter = 0;
    let mut iter: u16 = 0;
    let mut counter: usize = 0;
    let mut edges = 0;
    let mut prio = 0;

    loop {
        iter += 1;
        if terminate.load(Ordering::Relaxed) {
            break;
        }

        if iter == 2 {
            counter = 0;
        }
        end_iteration.store(false, Ordering::Relaxed);

        loop {
            //=========================================
            // Sottoiterazione
            //=========================================
            subiter += 1;

            let old_prio = prio;
            prio = current_priority.load(Ordering::Relaxed);
            let max_prio = mapper.bucket_span(prio).1;

            // estraggo batch dalla coda condivisa
            if vgc_threshold == 1 {
                while let Some(u) = local_queues.current_mut().pop_first(prio) {
                    info.set_last_update(u, iter);
                    edges += info.degree_of(u) as usize;
                    compute_index(
                        u,
                        &info,
                        offsets,
                        neighbors,
                        &mut count,
                        &mut temp,
                        max_prio,
                        old_prio,
                        &mut counter,
                        iter,
                        &mut local_queues,
                    );
                }
            } else {
                while let Some(u) = local_queues.current_mut().pop_node(prio) {
                    info.set_last_update(u, iter);
                    edges += info.degree_of(u) as usize;
                    compute_index(
                        u,
                        &info,
                        offsets,
                        neighbors,
                        &mut count,
                        &mut temp,
                        max_prio,
                        old_prio,
                        &mut counter,
                        iter,
                        &mut local_queues,
                    );
                }
            }

            phase_barrier.wait();
            local_queues.current_mut().flush(usize::MAX);

            // l'ultimo thread a finire aggiorna le variabili di controllo
            if threads_working.fetch_sub(1, Ordering::Relaxed) == 1 {
                // ultimo thread a finire
                threads_working.store(num_threads, Ordering::Relaxed);

                let new_prio = shared_pq.estimate_cutoff(target_batches_per_subiteration);

                if let Some(p) = new_prio {
                    current_priority.store(p, Ordering::Relaxed);
                } else {
                    /*
                    println!(
                        "Iterazione: {}, archi: {}",
                        iter,
                        edges_processed.load(Ordering::Relaxed) as f64
                            / offsets[offsets.len() - 1] as f64
                    );
                    */
                    end_iteration.store(true, Ordering::Relaxed);
                }
            }
            phase_barrier.wait();
            if end_iteration.load(Ordering::Relaxed) {
                edges_processed.fetch_add(edges, Ordering::Relaxed);
                edges = 0;
                break;
            }
        }
        local_queues.flip();
        local_queues.current_mut().flush(usize::MAX);

        //l'ultimo thread a finire controlla se terminare
        if threads_working.fetch_sub(1, Ordering::Relaxed) == 1 {
            // ultimo thread a finire
            threads_working.store(num_threads, Ordering::Relaxed);
            let new_prio = shared_pq.estimate_cutoff(target_batches_per_subiteration);
            if let Some(p) = new_prio {
                current_priority.store(p, Ordering::Relaxed);
            } else {
                current_priority.store(0, Ordering::Relaxed);
                terminate.store(true, Ordering::Relaxed);
            }
        }
        phase_barrier.wait();
    }
    counter += local_queues.current_mut().edges;
    counter += local_queues.next_mut().edges;
    current_priority.fetch_add(counter, Ordering::Relaxed);
    edges_processed.fetch_add(edges, Ordering::Relaxed);
    let mut vgc_t = vgc_threshold;

    if !vgc_enabled {
        vgc_t = 0;
    }

    if threads_working.fetch_sub(1, Ordering::Relaxed) == 1 {
        // scrivo misurazioni su out_file
        // algorithm, graph, num_threads, time, work, speed, vgc_threshold, batch_size, batches_per_subiter
        let mut out = OpenOptions::new()
            .write(true)
            .create(true)
            .append(true)
            .open(out_file)
            .expect("Impossibile aprire file di output");
        writeln!(
            out,
            "{}, {}, {}, {:.6}, {:.2}, {:.2}, {}, {}, {}",
            alg_name,
            graph_name,
            num_threads,
            start_t.elapsed().as_secs_f64(),
            edges_processed.load(Ordering::Relaxed) as f64 / offsets[offsets.len() - 1] as f64,
            (edges_processed.load(Ordering::Relaxed) as f64 / start_t.elapsed().as_micros() as f64),
            vgc_t,
            batch_budget.max_nodes,
            target_batches_per_subiteration
        )
        .expect("Impossibile scrivere sul file di output");
        println!(
            "[VGC: {}] Archi: {}, iterazioni: {}, sottoiterazioni totali: {}, archi anticipati: {}",
            vgc_t,
            edges_processed.load(Ordering::Relaxed) as f64 / offsets[offsets.len() - 1] as f64,
            iter,
            subiter,
            current_priority.load(Ordering::Relaxed) as f64 / offsets[offsets.len() - 1] as f64
        );
        println!(
            "Tempo: {:?} ({} archi/µs)",
            start_t.elapsed(),
            (edges_processed.load(Ordering::Relaxed) / start_t.elapsed().as_micros() as usize)
        );
    }
}

#[derive(Parser, Debug)]
pub struct Args {
    /// Path del file di input
    input: String,

    /// Esegue l'esperimento di speedup senza pinning
    #[arg(long)]
    speedup_no_pin: bool,

    /// Esegue l'esperimento di speedup con pinning
    #[arg(long)]
    speedup_pin: bool,

    /// Esegue l'esperimento di speedup con il pinning peggiore
    #[arg(long)]
    speedup_worst: bool,

    /// Esegue l'esperimento con hyperthreading con 8, 16, 32 e 64 thread
    #[arg(long)]
    hyperthreading: bool,

    /// Esegue l'esperimento senza hyperthreading con 8, 16, 32 e 64 thread
    #[arg(long)]
    no_hyperthreading: bool,

    /// Testa tutti i parametri con hyperthreading con 8 e 16 thread (batch size, vgc threshold, target batches per subiteration)
    #[arg(long)]
    test_all_parameters_ht: bool,

    /// Testa tutti i parametri senza hyperthreading con 8 e 16 thread (batch size, vgc threshold, target batches per subiteration)
    #[arg(long)]
    test_all_parameters_no_ht: bool,

    /// Esperimento con i parametri dati da linea di comando senza hyperthreading
    #[arg(long)]
    normal_run: bool,

    /// Esegue tutti gli esperimenti disponibili
    #[arg(long)]
    all: bool,

    /// Setta il numero di thread per l'esperimento
    #[arg(long, default_value_t = 8)]
    threads: usize,

    /// Setta la dimensione massima del batch per l'esperimento
    #[arg(long, default_value_t = 1024)]
    batch_size: usize,

    /// Setta il numero massimo di batch per sottoiterazione
    #[arg(long, default_value_t = 10)]
    target_batches_per_subiteration: usize,

    /// Setta la soglia VGC per l'esperimento
    #[arg(long, default_value_t = 0)]
    vgc_threshold: usize,
}

fn main() -> std::io::Result<()> {
    // leggo file su cui fare esperimenti, è passato da linea di comando
    let args = Args::parse();

    pin_thread_strict(0, &pinning_arrays::SAME_CLUSTER_NO_HYPERTHREADING);

    let mut graph = Graph::parse_file(&args.input, &pinning_arrays::SAME_CLUSTER_NO_HYPERTHREADING);

    if args.all || args.speedup_no_pin {
        speedup_no_pin(&args, &mut graph)?;
    }

    if args.all || args.speedup_pin {
        speedup_pin_ht(&args, &mut graph)?;
        speedup_pin_no_ht(&args, &mut graph)?;
    }

    if args.all || args.speedup_worst {
        speedup_worst_cfg(&args, &mut graph)?;
    }

    if args.all || args.hyperthreading {
        run_hyperthreading(&args, &mut graph)?;
    }

    if args.all || args.no_hyperthreading {
        run_no_hyperthreading(&args, &mut graph)?;
    }

    if args.all || args.test_all_parameters_ht {
        run_different_parameters_ht(&args, &mut graph)?;
    }

    if args.all || args.test_all_parameters_no_ht {
        run_different_parameters_no_ht(&args, &mut graph)?;
    }

    if args.all || args.normal_run {
        run_normal(&args, &mut graph)?;
    }

    Ok(())
}

pub fn speedup_no_pin(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/speedup.csv";
    let pinning = [500; 128];

    let num_threads = vec![
        1, 2, 4, 6, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 64, 96, 128,
    ];

    let times = 3;
    println!("Starting speedup no pinning experiment...");

    for &threads in &num_threads {
        println!("  {} threads...", threads);
        for _ in 0..times {
            graph.fastk(
                threads,
                args.batch_size,
                args.vgc_threshold > 0,
                args.vgc_threshold,
                out_file,
                args.target_batches_per_subiteration,
                &pinning,
                "NoPin",
            );
        }
    }

    Ok(())
}

pub fn speedup_pin_ht(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/speedup.csv";
    let pinning = pinning_arrays::SAME_CLUSTER_WITH_HYPERTHREADING;

    let num_threads = vec![
        2, 4, 6, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 64, 96, 128,
    ];

    let times = 3;
    println!("Starting speedup pinning with hyperthreading experiment...");
    for &threads in &num_threads {
        println!("  {} threads...", threads);
        for _ in 0..times {
            graph.fastk(
                threads,
                args.batch_size,
                args.vgc_threshold > 0,
                args.vgc_threshold,
                out_file,
                args.target_batches_per_subiteration,
                &pinning,
                "PinHT",
            );
        }
    }

    Ok(())
}

pub fn speedup_pin_no_ht(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/speedup.csv";
    let pinning = pinning_arrays::SAME_CLUSTER_NO_HYPERTHREADING;

    let num_threads = vec![
        2, 4, 6, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 64, 96, 128,
    ];

    let times = 3;
    println!("Starting speedup pinning without hyperthreading experiment...");
    for &threads in &num_threads {
        println!("  {} threads...", threads);
        for _ in 0..times {
            graph.fastk(
                threads,
                args.batch_size,
                args.vgc_threshold > 0,
                args.vgc_threshold,
                out_file,
                args.target_batches_per_subiteration,
                &pinning,
                "PinNoHT",
            );
        }
    }

    Ok(())
}

pub fn speedup_worst_cfg(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/speedup.csv";
    let pinning = pinning_arrays::WORST_CONFIG;

    let num_threads = vec![
        2, 4, 6, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 64, 96, 128,
    ];

    let times = 3;
    println!("Starting speedup worst-case pinning experiment...");
    for &threads in &num_threads {
        println!("  {} threads...", threads);
        for _ in 0..times {
            graph.fastk(
                threads,
                args.batch_size,
                args.vgc_threshold > 0,
                args.vgc_threshold,
                out_file,
                args.target_batches_per_subiteration,
                &pinning,
                "PinWorst",
            );
        }
    }

    Ok(())
}

pub fn run_hyperthreading(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/pinning_strategies.csv";
    let pinning = pinning_arrays::SAME_CLUSTER_WITH_HYPERTHREADING;

    let num_threads = vec![8, 16, 32, 64];

    let times = 3;
    println!("Starting hyperthreading experiment...");
    for &threads in &num_threads {
        println!("  {} threads...", threads);
        for _ in 0..times {
            graph.fastk(
                threads,
                args.batch_size,
                args.vgc_threshold > 0,
                args.vgc_threshold,
                out_file,
                args.target_batches_per_subiteration,
                &pinning,
                "HT",
            );
        }
    }

    Ok(())
}

pub fn run_no_hyperthreading(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/pinning_strategies.csv";
    let pinning = pinning_arrays::SAME_CLUSTER_NO_HYPERTHREADING;

    let num_threads = vec![8, 16];

    let times = 3;
    println!("Starting no hyperthreading experiment...");
    for &threads in &num_threads {
        println!("  {} threads...", threads);
        for _ in 0..times {
            graph.fastk(
                threads,
                args.batch_size,
                args.vgc_threshold > 0,
                args.vgc_threshold,
                out_file,
                args.target_batches_per_subiteration,
                &pinning,
                "noHT",
            );
        }
    }

    Ok(())
}

pub fn run_different_parameters_no_ht(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/parameters.csv";
    let pinning = pinning_arrays::SAME_CLUSTER_NO_HYPERTHREADING;

    let num_threads = vec![8, 16];
    let batch_sizes = vec![1, 16, 64, 256, 1024];
    let vgc_thresholds = vec![0, 4, 16, 64, 256];
    let batches_per_subiter = vec![1, 5, 10, 20];

    let times = 3;
    println!("Starting parameters hyperthreading experiment...");
    for &threads in &num_threads {
        for &batch_size in &batch_sizes {
            println!("  {} threads, batch size {}...", threads, batch_size);
            for _ in 0..times {
                graph.fastk(
                    threads,
                    batch_size,
                    args.vgc_threshold > 0,
                    args.vgc_threshold,
                    out_file,
                    args.target_batches_per_subiteration,
                    &pinning,
                    "noHT",
                );
            }
        }
        for &vgc_threshold in &vgc_thresholds {
            println!("  {} threads, vgc threshold {}...", threads, vgc_threshold);
            for _ in 0..times {
                graph.fastk(
                    threads,
                    args.batch_size,
                    vgc_threshold > 0,
                    vgc_threshold,
                    out_file,
                    args.target_batches_per_subiteration,
                    &pinning,
                    "noHT",
                );
            }
        }
        for &target_batches in &batches_per_subiter {
            println!(
                "  {} threads, target batches per subiteration {}...",
                threads, target_batches
            );
            for _ in 0..times {
                graph.fastk(
                    threads,
                    args.batch_size,
                    args.vgc_threshold > 0,
                    args.vgc_threshold,
                    out_file,
                    target_batches,
                    &pinning,
                    "noHT",
                );
            }
        }
    }

    Ok(())
}

pub fn run_different_parameters_ht(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/parameters.csv";
    let pinning = pinning_arrays::SAME_CLUSTER_WITH_HYPERTHREADING;

    let num_threads = vec![8, 16];
    let batch_sizes = vec![1, 16, 64, 256, 1024];
    let vgc_thresholds = vec![0, 4, 16, 64, 256];
    let batches_per_subiter = vec![1, 5, 10, 20];

    let times = 3;

    for &threads in &num_threads {
        for &batch_size in &batch_sizes {
            for _ in 0..times {
                graph.fastk(
                    threads,
                    batch_size,
                    args.vgc_threshold > 0,
                    args.vgc_threshold,
                    out_file,
                    args.target_batches_per_subiteration,
                    &pinning,
                    "HT",
                );
            }
        }
        for &vgc_threshold in &vgc_thresholds {
            for _ in 0..times {
                graph.fastk(
                    threads,
                    args.batch_size,
                    vgc_threshold > 0,
                    vgc_threshold,
                    out_file,
                    args.target_batches_per_subiteration,
                    &pinning,
                    "HT",
                );
            }
        }
        for &target_batches in &batches_per_subiter {
            for _ in 0..times {
                graph.fastk(
                    threads,
                    args.batch_size,
                    args.vgc_threshold > 0,
                    args.vgc_threshold,
                    out_file,
                    target_batches,
                    &pinning,
                    "HT",
                );
            }
        }
    }

    Ok(())
}

pub fn run_normal(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/final_runs.csv";
    let pinning = pinning_arrays::SAME_CLUSTER_NO_HYPERTHREADING;

    let times = 3;

    for _ in 0..times {
        graph.fastk(
            args.threads,
            args.batch_size,
            args.vgc_threshold > 0,
            args.vgc_threshold,
            out_file,
            args.target_batches_per_subiteration,
            &pinning,
            "HT",
        );
    }

    Ok(())
}

#[inline(always)]
pub fn compute_index(
    u: usize,
    nodes: &InfoStore,
    offsets: &[u32],
    neighbors: &[u32],
    count: &mut Vec<u32>,
    temp: &mut Vec<(usize, u32)>,
    current_prio: usize,
    old_prio: usize,
    counter: &mut usize,
    iter: u16,
    dual: &mut DualLocalPQ,
) {
    let estab = nodes.load_estab(u, Ordering::SeqCst);
    let old_stab = estab::stability(estab);
    let k = estab::estimate(estab);
    if k >= count.len() as u32 {
        count.resize(k as usize + 1, 0);
    }

    if old_stab >= 0 {
        *counter += 1;
    }

    count[..=k as usize].fill(0);

    let mut index;
    for neighbor in neighbors_slice(offsets, neighbors, u) {
        let neighbor_estab = nodes.load_estab(*neighbor as usize, Ordering::Relaxed);
        let neighbor_est = estab::estimate(neighbor_estab);

        if neighbor_est > k {
            index = k;
            if neighbor_est <= current_prio as u32 {
                temp.push((*neighbor as usize, neighbor_est));
            }
        } else {
            temp.push((*neighbor as usize, neighbor_est));
            index = neighbor_est;
        }
        count[index as usize] += 1;
    }

    let mut i = k as usize;
    let mut stability = 0;

    while i > 1 {
        count[i - 1] += count[i];
        if count[i] as usize >= i {
            stability = (count[i] as i32) - (i as i32);
            break;
        }
        i -= 1;
    }
    if !nodes.publish_estab(u, i as u32, old_stab, stability) {
        // la nuova stima non è più affidabile, va ricalcolata
        // la stima è comunque cambiata, quindi faccio i decrementi di stability sui vicini
        // con estimate compresa tra i e k
        for (v, neighbor_est) in temp.drain(..) {
            if neighbor_est <= i as u32 {
                continue;
            }
            let result = nodes.fetch_update_stability(v, 1, k, i as u32);

            if let Some((estab_v, crossed)) = result {
                if crossed {
                    dual.push_node(
                        estab::estimate(estab_v) as usize,
                        old_prio,
                        v,
                        nodes.degree_of(v) as usize,
                        nodes.get_last_update(v),
                        iter,
                    );
                }
            }
        }
        compute_index(
            u,
            nodes,
            offsets,
            neighbors,
            count,
            temp,
            current_prio,
            old_prio,
            counter,
            iter,
            dual,
        );
        return;
    }

    for (v, neighbor_est) in temp.drain(..) {
        if neighbor_est <= i as u32 {
            continue;
        }
        let result = nodes.fetch_update_stability(v, 1, k, i as u32);

        if let Some((estab_v, crossed)) = result {
            if crossed {
                dual.push_node(
                    estab::estimate(estab_v) as usize,
                    old_prio,
                    v,
                    nodes.degree_of(v) as usize,
                    nodes.get_last_update(v),
                    iter,
                );
            }
        }
    }
}

fn _write_to_file(path: &str, core: Vec<u32>) -> std::io::Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create(true)
        .append(true)
        .open(path)?;

    for u in core.iter() {
        writeln!(file, "{}", u)?;
    }
    Ok(())
}

/// Pinna il thread corrente al core logico indicato da pinning[tid].
pub fn pin_thread_strict(tid: usize, pinning: &[usize]) {
    assert!(
        tid < pinning.len(),
        "Thread id {} fuori dai limiti della slice di pinning (len = {})",
        tid,
        pinning.len()
    );

    let cpu_id = pinning[tid];

    let core_id = CoreId { id: cpu_id };

    core_affinity::set_for_current(core_id);
}

pub fn pin_test(args: &Args, graph: &Graph) -> std::io::Result<()> {
    // hardcoded file su cui scrivere i risultati
    let out_file = "./results/final_runs.csv";
    let pinning = pinning_arrays::TEST;

    let times = 3;

    for _ in 0..times {
        graph.fastk(
            args.threads,
            args.batch_size,
            args.vgc_threshold > 0,
            args.vgc_threshold,
            out_file,
            args.target_batches_per_subiteration,
            &pinning,
            "HT",
        );
    }

    Ok(())
}
