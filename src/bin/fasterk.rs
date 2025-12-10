#![allow(dead_code)]
use parking_lot::Mutex;
use std::cell::UnsafeCell;
use std::collections::VecDeque;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::BufRead;
use std::io::BufReader;
use std::io::Write;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::Instant;

fn write_to_file(path: &str, core: Vec<u32>) -> std::io::Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(path)?;

    for u in core.iter() {
        writeln!(file, "{}", u)?;
    }
    Ok(())
}

#[inline(always)]
fn neighbors_slice<'a>(offsets: &'a [usize], neighbors: &'a [usize], v: usize) -> &'a [usize] {
    let start = offsets[v];
    let end = offsets[v + 1];
    &neighbors[start..end]
}

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Questo modulo richiede un usize a 64 bit (target_pointer_width = 64).");

pub mod estab {

    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    pub const SHIFT: usize = 32;
    pub const EST_MASK: usize = 0xFFFF_FFFF;
    pub const STAB_MASK: usize = 0xFFFF_FFFF_0000_0000;

    // ---------- pack/unpack con stability firmata (i32) ----------
    #[inline(always)]
    pub const fn pack(stability_i32: i32, estimate: u32) -> usize {
        ((stability_i32 as u32 as usize) << SHIFT) | (estimate as usize)
    }

    #[inline(always)]
    pub const fn estimate(x: usize) -> u32 {
        (x & EST_MASK) as u32
    }

    #[inline(always)]
    pub const fn stability(x: usize) -> i32 {
        // sign-extend dei 32 bit alti
        ((x >> SHIFT) as u32) as i32
    }

    #[inline(always)]
    pub const fn set_estimate(x: usize, est: u32) -> usize {
        (x & STAB_MASK) | (est as usize)
    }

    #[inline(always)]
    pub const fn set_stability(x: usize, stab_i32: i32) -> usize {
        (x & EST_MASK) | (((stab_i32 as u32) as usize) << SHIFT)
    }

    /// Decrementa stability di 'delta' se estimate è compresa tra old_est (escluso) e new_est (incluso).
    /// Restituisce Some((new_stab, crossed)) se l'aggiornamento è avvenuto, None altrimenti. crossed è true se si è passati da stability non negativa a negativa.
    #[inline(always)]
    pub fn fetch_update_stability(
        a: &AtomicUsize,
        delta: i32,
        old_est: u32,
        new_est: u32,
        max: i32,
    ) -> Option<(usize, bool)> {
        if !(new_est < old_est) {
            return None;
        }
        match a.fetch_update(Ordering::SeqCst, Ordering::Relaxed, |cur| {
            let est = self::estimate(cur);

            let s = self::stability(cur);
            if (new_est < est && est <= old_est) || (new_est < est && s <= max) {
                let new_stability = s - delta;
                Some(self::set_stability(cur, new_stability))
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
    /// Restituisce true se la nuova stability è non negativa. Altrimenti restituisce false, che
    /// significa che la stima appena calcolata non è più affidabile e va ricalcolata.
    #[inline(always)]
    pub fn publish_estab(a: &AtomicUsize, new_est: u32, old_stab: i32, new_stab: i32) -> bool {
        let delta = new_stab - old_stab;
        let result = a
            .fetch_update(Ordering::SeqCst, Ordering::Relaxed, |cur| {
                let current_stab = self::stability(cur);
                let next_stab = current_stab + delta;
                let temp = self::set_estimate(cur, new_est);
                Some(self::set_stability(temp, next_stab))
            })
            .expect("error in publish_estab");

        if stability(result) + delta < 0 {
            return false;
        }
        true
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
    max_degree: i32,
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
            max_degree: 0,
        }
    }
    #[inline(always)]
    pub fn load_estab(&self, id: usize, ordering: Ordering) -> usize {
        self.estimate_stability[id].load(ordering)
    }

    #[inline(always)]
    pub fn store_estab(&self, id: usize, (estimate, stability): (u32, i32)) {
        self.estimate_stability[id].store(estab::pack(stability, estimate), Ordering::Relaxed);
    }
    /// Imposta stability a -max_degree e restituisce il valore precedente.
    /// Usato all'inizio di compute_index, per comunicare che il nodo è in fase di elaborazione.
    pub fn fetch_and_set_stability(&self, id: usize) -> usize {
        let prev = self.estimate_stability[id]
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |cur| {
                Some(estab::set_stability(cur, -self.max_degree))
            })
            .expect("fatal error fetch_and_set_stability");
        prev
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
        estab::fetch_update_stability(
            &self.estimate_stability[id],
            delta,
            old_est,
            new_est,
            self.max_degree as i32,
        )
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
    pub fn set_last_update(&self, id: usize, iter: usize) {
        unsafe {
            (*self.info_cell_mut(id)).0.last_update = iter as u16;
        }
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

// ==============================================
// Batch, code locali e coda condivisa batchizzata
// ==============================================

#[derive(Debug)]
pub struct Batch {
    pub prio: usize,       // livello (monolivello)
    pub edges: usize,      // somma dei gradi dei nodi
    pub nodes: Vec<usize>, // nodi (no-copy)
}
impl Batch {
    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

#[derive(Copy, Clone, Debug)]
pub struct BatchBudget {
    pub min_nodes: usize, // soglia di chiusura
    pub max_nodes: usize, // limite duro
    pub max_edges: usize, // limite duro (attivo se len >= min_nodes)
}

// Coda locale: per ogni livello l'ultimo elemento è il batch aperto
pub struct BatchPQ {
    buckets: Vec<VecDeque<Batch>>,
    budget: BatchBudget,
    first_non_empty: usize,
}

impl BatchPQ {
    pub fn new(budget: BatchBudget) -> Self {
        Self {
            buckets: Vec::new(),
            budget,
            first_non_empty: 0,
        }
    }

    #[inline]
    pub fn ensure_level(&mut self, k: usize) {
        if k >= self.buckets.len() {
            self.buckets.resize_with(k + 1, VecDeque::new);
        }
    }

    #[inline]
    pub fn push_node(&mut self, prio: usize, node: usize, deg: usize) {
        self.ensure_level(prio);

        if prio < self.first_non_empty {
            self.first_non_empty = prio;
        }

        if self.buckets[prio].is_empty() {
            self.buckets[prio].push_back(Batch {
                prio,
                edges: deg,
                nodes: vec![node],
            });
            return;
        }
        let batch = self.buckets[prio].back_mut().unwrap();
        batch.edges += deg;
        batch.nodes.push(node);
        if batch.len() >= self.budget.min_nodes {
            if batch.edges > self.budget.max_edges || batch.len() >= self.budget.max_nodes {
                self.buckets[prio].push_back(Batch {
                    prio,
                    edges: 0,
                    nodes: Vec::with_capacity(self.budget.max_nodes),
                })
            }
        }
    }
    pub fn is_empty(&self) -> bool {
        self.buckets.iter().all(|q| q.is_empty())
    }

    pub fn need_merge(&self, cutoff: usize) -> bool {
        for q in self.buckets.iter().take(cutoff.saturating_add(1)) {
            if q.len() >= 2 {
                return true;
            }
        }
        false
    }

    fn sync_first_non_empty(&mut self) {
        self.first_non_empty = 0;
        while self.first_non_empty < self.buckets.len()
            && self.buckets[self.first_non_empty].is_empty()
        {
            self.first_non_empty += 1;
        }
    }

    pub fn pop_batch(&mut self, cutoff: usize) -> Option<Batch> {
        if self.first_non_empty >= self.buckets.len() {
            return None;
        }
        while self.first_non_empty < self.buckets.len()
            && self.buckets[self.first_non_empty].is_empty()
        {
            self.first_non_empty += 1;
        }
        if self.first_non_empty >= self.buckets.len() || self.first_non_empty > cutoff {
            return None;
        }
        let batch = self.buckets[self.first_non_empty].pop_front();
        batch
    }

    pub fn merge_from(&mut self, other: &mut Self, cutoff: usize) {
        // fonde la coda locale con la coda condivisa fino al livello cutoff incluso,
        // lascia l'ultimo elemento della coda locale, perché è un batch aperto
        self.ensure_level(cutoff);
        other.ensure_level(cutoff);
        for i in 0..=cutoff {
            while other.buckets[i].len() >= 2 {
                self.first_non_empty = self.first_non_empty.min(i);
                self.buckets[i].push_back(other.buckets[i].pop_front().unwrap());
            }
            if other.buckets[i].len() == 1
                && other.buckets[i].front().unwrap().len() > self.budget.min_nodes
            {
                self.buckets[i].push_back(other.buckets[i].pop_front().unwrap());
            }
        }
    }

    pub fn force_merge_from(&mut self, other: &mut Self) {
        self.ensure_level(other.buckets.len().saturating_sub(1));
        other.ensure_level(self.buckets.len().saturating_sub(1));
        self.first_non_empty = self.first_non_empty.min(other.first_non_empty);
        for i in other.first_non_empty..self.buckets.len().max(other.buckets.len()) {
            while !other.buckets[i].is_empty() {
                self.buckets[i].push_back(other.buckets[i].pop_front().unwrap());
            }
        }
        other.first_non_empty = other.buckets.len();
    }

    pub fn estimate_cutoff(&self, target_batches_per_subiter: usize) -> usize {
        let mut cutoff = self.first_non_empty;
        let mut sum = 0;
        while sum < target_batches_per_subiter && cutoff < self.buckets.len() {
            sum += self.buckets[cutoff].len();
            cutoff += 1;
        }
        cutoff
    }

    pub fn estimate_cutoff_relative(
        &self,
        target_batches_per_subiter: usize,
        last_cutoff: usize,
    ) -> usize {
        let mut cutoff = last_cutoff;
        let mut sum = 0;

        while sum < target_batches_per_subiter && cutoff < self.buckets.len() {
            sum += self.buckets[cutoff].len();
            cutoff += 1;
        }
        cutoff
    }

    pub fn length(&self) -> usize {
        self.buckets.iter().map(|q| q.len()).sum()
    }
    pub fn batches_in_queue(&self) -> usize {
        self.buckets.iter().map(|q| q.iter().len()).sum()
    }
}

pub struct DualPQLocal {
    queues: [BatchPQ; 2],
    cur: usize, // 0 o 1
}

impl DualPQLocal {
    pub fn new(budget: BatchBudget) -> Self {
        Self {
            queues: [BatchPQ::new(budget), BatchPQ::new(budget)],
            cur: 0,
        }
    }

    #[inline]
    pub fn current_mut(&mut self) -> &mut BatchPQ {
        &mut self.queues[self.cur]
    }

    #[inline]
    pub fn next_mut(&mut self) -> &mut BatchPQ {
        &mut self.queues[self.cur ^ 1]
    }

    /// Scambia current e next (da chiamare a fine **iterazione**, non di sottoiterazione).
    #[inline]
    pub fn flip(&mut self) {
        self.cur ^= 1;
    }

    #[inline]
    pub fn merge_to_next(&mut self) {
        let (left, right) = self.queues.split_at_mut(1);

        let (current, next) = if self.cur == 0 {
            (&mut left[0], &mut right[0])
        } else {
            (&mut right[0], &mut left[0])
        };

        next.force_merge_from(current);
    }
}

pub struct DualPQShared {
    queues: [Arc<Mutex<BatchPQ>>; 2],
    cur: AtomicUsize, // 0 o 1
}
unsafe impl Send for DualPQShared {}
unsafe impl Sync for DualPQShared {}

impl DualPQShared {
    pub fn new(budget: BatchBudget) -> Arc<Self> {
        Arc::new(Self {
            queues: [
                Arc::new(Mutex::new(BatchPQ::new(budget))),
                Arc::new(Mutex::new(BatchPQ::new(budget))),
            ],
            cur: AtomicUsize::new(0),
        })
    }

    #[inline]
    pub fn current(&self) -> Arc<Mutex<BatchPQ>> {
        let i = self.cur.load(Ordering::Relaxed) & 1;
        Arc::clone(&self.queues[i])
    }

    #[inline]
    pub fn next(&self) -> Arc<Mutex<BatchPQ>> {
        let i = self.cur.load(Ordering::Relaxed) ^ 1;
        Arc::clone(&self.queues[i & 1])
    }

    /// Flip di iterazione (il coordinatore lo invoca una sola volta a fine iterazione).
    pub fn flip(&self) {
        let old = self.cur.load(Ordering::Relaxed) & 1;
        let newi = old ^ 1;
        self.cur.store(newi, Ordering::Release);
    }
}

pub struct Graph {
    pub num_nodes: usize,
    pub offsets: Vec<usize>,
    pub neighbors: Vec<usize>,
    pub avg_deg: usize,
    pub max_deg: usize,
}
impl Graph {
    pub fn parse_file(path: &str) -> Self {
        let file = BufReader::new(File::open(path).expect("File inesistente"));
        let mut edges = vec![];
        let mut max_node = 0;

        for line in file.lines() {
            let line = line.unwrap();
            if line.starts_with('#') || line.trim().is_empty() {
                continue;
            }
            let mut parts = line.split_whitespace();
            let u: usize = parts.next().unwrap().parse().unwrap();
            let v: usize = parts.next().unwrap().parse().unwrap();
            max_node = max_node.max(u).max(v);
            edges.push((u, v));
            edges.push((v, u));
        }

        let num_nodes = max_node + 1;
        let mut degree = vec![0; num_nodes];
        for &(u, _) in &edges {
            degree[u] += 1;
        }

        let mut offsets = vec![0; num_nodes + 1];
        let mut max_deg = 0;
        for i in 0..num_nodes {
            offsets[i + 1] = offsets[i] + degree[i];
            max_deg = max_deg.max(degree[i]);
        }

        let mut neighbors = vec![0; offsets[num_nodes]];
        let mut fill = vec![0; num_nodes];
        for i in 0..num_nodes {
            fill[i] = offsets[i];
        }

        for &(u, v) in &edges {
            neighbors[fill[u]] = v;
            fill[u] += 1;
        }

        //calcolo il grado medio

        Graph {
            num_nodes,
            offsets,
            neighbors,
            max_deg: max_deg,
            avg_deg: edges.len() / num_nodes,
        }
    }

    #[inline(always)]
    pub fn neighbors_of(&self, u: usize) -> &[usize] {
        let (s, e) = (self.offsets[u], self.offsets[u + 1]);
        &self.neighbors[s..e]
    }

    #[inline(always)]
    pub fn degree_of(&self, u: usize) -> usize {
        self.offsets[u + 1] - self.offsets[u]
    }

    pub fn fastk(&self, num_threads: usize, chunk_size: usize) -> Vec<u32> {
        // Parametri
        let batch_budget = BatchBudget {
            min_nodes: 1,
            max_nodes: chunk_size, // cardinalità massima per batch
            max_edges: self.avg_deg * chunk_size, // budget in archi per batch
        };

        let info = Arc::new(InfoStore::new(self.num_nodes));

        // DualQueue condivisa
        let dual = DualPQShared::new(batch_budget);

        // Barriera condivisa
        let phase_barrier = Arc::new(Barrier::new(num_threads));

        // Controllo coordinatore/worker
        let end_iteration = Arc::new(AtomicBool::new(false));
        let terminate = Arc::new(AtomicBool::new(false));
        let current_priority = Arc::new(AtomicUsize::new(2));

        let nodes: &[usize] = &self.offsets;
        let edges: &[usize] = &self.neighbors;

        let threads_working = Arc::new(AtomicUsize::new(num_threads));

        let edges_processed = Arc::new(AtomicUsize::new(0));

        let start = Instant::now();
        thread::scope(|scope| {
            for tid in 0..num_threads {
                let info = Arc::clone(&info);
                let dual = Arc::clone(&dual);
                let phase_barrier = Arc::clone(&phase_barrier);
                let offsets = nodes;
                let neighbors = edges;
                let end_iteration = Arc::clone(&end_iteration);
                let terminate = Arc::clone(&terminate);
                let current_priority = Arc::clone(&current_priority);
                let threads_working = Arc::clone(&threads_working);
                let edges_processed = Arc::clone(&edges_processed);
                scope.spawn(move || {
                    thread_routine(
                        tid,
                        info,
                        dual,
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
                    )
                });
            }
        });
        println!(
            "Elaborati {} archi in totale in {:?}",
            edges_processed.load(Ordering::Relaxed) as f64 / self.offsets[self.num_nodes] as f64,
            start.elapsed()
        );
        return (0..self.num_nodes)
            .map(|u| estab::estimate(info.load_estab(u, Ordering::Relaxed)))
            .collect();
    }
}

fn main() -> std::io::Result<()> {
    // gestione argomenti passati da linea di comando: in_file (file da parsare) e out_file (file su cui scrivere la coreness dei nodi)
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 || args.len() > 5 {
        println!("2 argomenti: file di input e file in cui scrivere, -t opzionale per settare il numero di thread");
        return Ok(());
    }
    let in_file = &args[1];
    let out_file = &args[2];
    let mut num_threads = 6;
    if args.len() == 5 {
        if args[3] == "-t" {
            num_threads = args[4].parse().unwrap_or(6);
        } else {
            return Ok(());
        }
    }
    let mut start = Instant::now();
    let graph = Graph::parse_file(in_file);

    println!("Per parsare il file: {:?}", start.elapsed());
    start = Instant::now();
    let core = graph.fastk(num_threads, 256);
    println!(
        "Per calcolare coreness con threads in {:?}",
        start.elapsed()
    );
    write_to_file(&out_file, core)?;
    // scrittura valori di coreness dei nodi

    Ok(())
}

#[inline(always)]
pub fn thread_routine(
    tid: usize,
    info: Arc<InfoStore>,
    dual: Arc<DualPQShared>,
    phase_barrier: Arc<Barrier>,
    offsets: &[usize],
    neighbors: &[usize],
    end_iteration: Arc<AtomicBool>,
    terminate: Arc<AtomicBool>,
    current_priority: Arc<AtomicUsize>,
    batch_budget: BatchBudget,
    threads_working: Arc<AtomicUsize>,
    edges_processed: Arc<AtomicUsize>,
    num_threads: usize,
) {
    //=================================================================
    // inizializzo coda dual locale
    let mut local_queue = DualPQLocal::new(batch_budget);
    let mut count: Vec<u32> = vec![0; 1024];

    let target_batches_per_subiteration = num_threads * 10;

    // prefilling disgiunto per owner: nessuna barriera necessaria
    // ogni thread si prende una parte in base al proprio tid

    let start_t = Instant::now();

    let n = info.num_nodes;
    let chunk = (n + num_threads - 1) / num_threads;
    let start = tid * chunk;
    let end = (start + chunk).min(n);

    for u in start..end {
        let deg = (offsets[u + 1] - offsets[u]) as u32;
        // inizializzo estimate e stability
        info.store_estab(u, (deg, -1 as i32));

        if deg > 1 {
            info.set_degree(u, deg);
            info.set_in_queue(u, true);
            info.set_last_update(u, 1);
            local_queue
                .current_mut()
                .push_node(deg as usize, u, info.degree_of(u) as usize);
        } else {
            info.set_degree(u, deg);
        }
    }

    {
        let cur = dual.current();
        let mut q = cur.lock();
        q.force_merge_from(local_queue.current_mut());
        let last_worker = threads_working.fetch_sub(1, Ordering::Relaxed) == 1;
        if last_worker {
            threads_working.store(num_threads, Ordering::Relaxed);
            current_priority.store(
                q.estimate_cutoff(target_batches_per_subiteration),
                Ordering::Relaxed,
            );
        }
    }

    phase_barrier.wait(); // barrier inizio iterazioni

    //===============================================================
    //==================INIZIO PROTOCOLLO==================
    //===============================================================

    let mut activated: Vec<(usize, u32)> = Vec::with_capacity(1024);
    let mut temp: Vec<(usize, u32)> = Vec::with_capacity(1024);

    let mut iter = 0;

    let mut prio_range: (usize, usize) = (0, 0);
    // (old_prio, current_prio)
    // se un nodo deve essere reinserito in coda, lo inserisco in next se è già stato processato in questa iterazione
    // oppure se la sua stima è minore di current_prio (quindi non verrà processato in questa sottoiterazione)

    let counter: &mut usize = &mut 0;
    let mut edges = 0;

    // pop da coda locale e condivisa
    // elaborazione nodi
    // reinserimento nodi attivati in coda locale next
    // merge in coda condivisa di next se necessario
    // ultimo thread setta current_priority e end_iteration

    // se end_iteration tutti fanno merge_to_next, flip locale e merge in coda condivisa
    // l'ultimo thread fa flip condiviso e setta terminate se next è vuota

    let mut last_subiter;
    loop {
        iter += 1;
        loop {
            prio_range.0 = prio_range.1;
            prio_range.1 = current_priority.load(Ordering::Relaxed);
            last_subiter = end_iteration.load(Ordering::Relaxed);

            let prio = prio_range.1;
            while let Some(batch) = local_queue.current_mut().pop_batch(prio) {
                edges += batch.edges;
                for &u in batch.nodes.iter() {
                    info.set_last_update(u, iter);
                    compute_index(
                        u,
                        &info,
                        offsets,
                        neighbors,
                        &mut count,
                        &mut activated,
                        &mut temp,
                        prio,
                        counter,
                        tid,
                    );
                    for (u, est) in activated.drain(..) {
                        let deg = info.degree_of(u) as usize;
                        if iter == info.get_info(u).0.last_update as usize {
                            // è già stato processato in questa iterazione
                            local_queue.next_mut().push_node(est as usize, u, deg);
                        } else {
                            local_queue.current_mut().push_node(est as usize, u, deg);
                        }
                    }
                }
            }

            loop {
                if let Some(batch) = {
                    let cur = dual.current();
                    let mut q = cur.lock();
                    q.pop_batch(prio)
                } {
                    edges += batch.edges;
                    for &u in batch.nodes.iter() {
                        compute_index(
                            u,
                            &info,
                            offsets,
                            neighbors,
                            &mut count,
                            &mut activated,
                            &mut temp,
                            prio,
                            counter,
                            tid,
                        );
                    }
                } else {
                    break;
                }
            }

            for (u, est) in activated.drain(..) {
                let deg = info.degree_of(u) as usize;
                info.set_last_update(u, iter);

                local_queue.next_mut().push_node(est as usize, u, deg);
            }

            let last_worker = threads_working.fetch_sub(1, Ordering::Relaxed) == 1;
            if last_worker {
                let cur = dual.current();
                let cur_q = cur.lock();
                if cur_q.is_empty() {
                    dual.flip();
                    end_iteration.store(true, Ordering::Relaxed);
                }
                let p = cur_q.estimate_cutoff(target_batches_per_subiteration);
                current_priority.store(p, Ordering::Relaxed);

                threads_working.store(num_threads, Ordering::Relaxed);
            }

            phase_barrier.wait(); // barrier fine sottoiterazione

            if last_subiter {
                break;
            }
        }
        local_queue.flip();
        {
            let q = dual.current();
            let mut q_lock = q.lock();
            q_lock.force_merge_from(local_queue.current_mut());
        }

        let last_worker = threads_working.fetch_sub(1, Ordering::Relaxed) == 1;
        if last_worker {
            let q = dual.current();
            let q_lock = q.lock();
            end_iteration.store(false, Ordering::Relaxed);
            if q_lock.is_empty() {
                terminate.store(true, Ordering::Relaxed);
            }
            let p = q_lock.estimate_cutoff(target_batches_per_subiteration);
            current_priority.store(p, Ordering::Relaxed);
            threads_working.store(num_threads, Ordering::Relaxed);
        }
        phase_barrier.wait(); // barrier fine iterazione
        if terminate.load(Ordering::Relaxed) {
            if last_worker {
                println!("Terminato in {} iterazioni", iter);
            }
            break;
        }
    }

    println!(
        "Thread {} ha finito in {:?}, ricalcoli: {}, archi processati: {}",
        tid,
        start_t.elapsed(),
        counter,
        edges as f64 / (offsets[offsets.len() - 1] as f64)
    );

    edges_processed.fetch_add(edges, Ordering::Relaxed);
}

#[inline(always)]
pub fn compute_index(
    u: usize,
    nodes: &InfoStore,
    offsets: &[usize],
    neighbors: &[usize],
    count: &mut Vec<u32>,
    activated: &mut Vec<(usize, u32)>,
    temp: &mut Vec<(usize, u32)>,
    current_prio: usize,
    counter: &mut usize,
    tid: usize,
) {
    let estab = nodes.load_estab(u, Ordering::SeqCst);
    let old_stab = estab::stability(estab);
    let k = estab::estimate(estab);
    if k >= count.len() as u32 {
        count.resize(k as usize + 1, 0);
    }

    count[..=k as usize].fill(0);

    let mut index;
    for neighbor in neighbors_slice(offsets, neighbors, u) {
        let neighbor_estab = nodes.load_estab(*neighbor, Ordering::Relaxed);
        let neighbor_est = estab::estimate(neighbor_estab);

        if neighbor_est > k {
            index = k;
            if neighbor_est <= current_prio as u32 {
                temp.push((*neighbor, neighbor_est));
            }
        } else {
            temp.push((*neighbor, neighbor_est));
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
                    activated.push((v, estab::estimate(estab_v)));
                }
            }
        }
        compute_index(
            u,
            nodes,
            offsets,
            neighbors,
            count,
            activated,
            temp,
            current_prio,
            counter,
            tid,
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
                activated.push((v, estab::estimate(estab_v)));
            }
        }
    }
}
