#![allow(dead_code)]
use parking_lot::Mutex;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use std::cell::UnsafeCell;
use std::collections::VecDeque;
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::io::BufRead;
use std::io::BufReader;
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::Instant;

// ============================
// Strutture di base per i nodi
// ============================

#[derive(Clone, Debug)]
pub struct InfoNode {
    pub estimate: u32,    // stima corrente
    pub stability: i32,   // slack/stability (può essere negativo)
    pub last_active: u16, // ultima iterazione in cui è entrato in coda
    pub deg: u32,         // grado
    pub in_queue: bool,   // è presente in una delle due code in questa iterazione
}

impl Default for InfoNode {
    fn default() -> Self {
        Self {
            estimate: 0,
            stability: 0,
            last_active: 0,
            deg: 0,
            in_queue: false,
        }
    }
}

// Contenitore condiviso degli InfoNode con mutazioni disgiunte per-owner.
pub struct InfoStore {
    inner: Vec<UnsafeCell<InfoNode>>,
}
unsafe impl Send for InfoStore {}
unsafe impl Sync for InfoStore {}

impl InfoStore {
    pub fn new(v: Vec<InfoNode>) -> Self {
        Self {
            inner: v.into_iter().map(UnsafeCell::new).collect(),
        }
    }
    #[inline]
    pub fn get(&self, i: usize) -> &UnsafeCell<InfoNode> {
        &self.inner[i]
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }
}

// Partizione a blocchi: assegna l'owner di ogni nodo
#[derive(Copy, Clone, Debug)]
pub struct OwnerMap {
    pub num_threads: usize,
    pub block: usize,
}
impl OwnerMap {
    #[inline(always)]
    pub fn owner_of(&self, v: usize) -> usize {
        (v / self.block) % self.num_threads
    }
}

#[inline(always)]
fn neighbors_slice<'a>(offsets: &'a [usize], neighbors: &'a [usize], v: usize) -> &'a [usize] {
    let start = offsets[v];
    let end = offsets[v + 1];
    &neighbors[start..end]
}

// =====================================
// Matrice SPSC lock-free per stability
// =====================================

#[repr(align(64))]
pub struct SpscSlot<T> {
    q: UnsafeCell<VecDeque<T>>,
}
unsafe impl<T: Send> Send for SpscSlot<T> {}
unsafe impl<T: Send> Sync for SpscSlot<T> {}
impl<T> SpscSlot<T> {
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            q: UnsafeCell::new(VecDeque::with_capacity(cap)),
        }
    }
    #[inline]
    pub unsafe fn push_back(&self, v: T) {
        (*self.q.get()).push_back(v);
    }
    #[inline]
    pub unsafe fn read_buffer_mut(&self) -> &mut VecDeque<T> {
        &mut *self.q.get()
    }
}

pub struct SpscMatrix<T> {
    slots: Vec<Vec<SpscSlot<T>>>,
    n: usize,
}
impl<T: Send> SpscMatrix<T> {
    pub fn new(num_threads: usize, cap_hint_per_slot: usize) -> Arc<Self> {
        let mut slots = Vec::with_capacity(num_threads);
        for _i in 0..num_threads {
            let mut row = Vec::with_capacity(num_threads);
            for _j in 0..num_threads {
                row.push(SpscSlot::with_capacity(cap_hint_per_slot));
            }
            slots.push(row);
        }
        Arc::new(Self {
            slots,
            n: num_threads,
        })
    }
    #[inline]
    pub unsafe fn send(&self, i: usize, j: usize, v: T) {
        self.slots[i][j].push_back(v);
    }
    #[inline]
    pub unsafe fn read_from(&self, i: usize, j: usize) -> &mut VecDeque<T> {
        self.slots[i][j].read_buffer_mut()
    }
}

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
        }
    }

    pub fn force_merge_from(&mut self, other: &mut Self) {
        let max = self.buckets.len().max(other.buckets.len()) - 1;
        self.ensure_level(max);
        other.ensure_level(max);
        for i in 0..=max {
            while !other.buckets[i].is_empty() {
                self.first_non_empty = self.first_non_empty.min(i);
                self.buckets[i].push_back(other.buckets[i].pop_front().unwrap());
            }
        }
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

// ===============
// Struttura Grafo
// ===============

pub struct Graph {
    pub num_nodes: usize,
    pub offsets: Vec<usize>,
    pub neighbors: Vec<usize>,
    pub core: Vec<usize>,
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
            core: Vec::from_iter((0..num_nodes).map(|_| 0)), // inizializza core a zero
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

    // ==========================
    // Algoritmo fastk (completo)
    // ==========================
    pub fn fastk(&mut self, num_threads: usize, chunk_size: usize) -> usize {
        // Parametri
        let batch_budget = BatchBudget {
            min_nodes: 12,
            max_nodes: chunk_size, // cardinalità massima per batch
            max_edges: self.avg_deg * chunk_size, // budget in archi per batch
        };
        let target_batches_per_subiteration = num_threads;
        let owner = OwnerMap {
            num_threads,
            block: 1024.max(self.num_nodes / (num_threads * 8).max(1)),
        };

        let start = Instant::now();
        // Stato per nodo
        let info_init: Vec<InfoNode> = (0..self.num_nodes)
            .into_par_iter()
            .map(|v| {
                let deg = (self.offsets[v + 1] - self.offsets[v]) as u32;
                InfoNode {
                    estimate: deg,
                    stability: 0,
                    last_active: 0,
                    deg,
                    in_queue: false,
                }
            })
            .collect();

        let info = Arc::new(InfoStore::new(info_init));

        // DualQueue condivisa
        let dual = DualPQShared::new(batch_budget);

        // Matrice SPSC
        let cap_hint = self.avg_deg.max(16);
        let channels: Arc<SpscMatrix<usize>> = SpscMatrix::new(num_threads, cap_hint);

        // Barriera condivisa
        let phase_barrier = Arc::new(Barrier::new(num_threads + 1));

        // Controllo coordinatore/worker
        let iterations = Arc::new(AtomicUsize::new(0));
        let end_iteration = Arc::new(AtomicBool::new(false));
        let terminate = Arc::new(AtomicBool::new(false));
        let current_priority = Arc::new(AtomicUsize::new(0));

        let nodes: &[usize] = &self.offsets;
        let edges: &[usize] = &self.neighbors;

        let threads_working = Arc::new(AtomicUsize::new(num_threads));

        let edges_processed = Arc::new(AtomicUsize::new(0));

        thread::scope(|scope| {
            for tid in 0..num_threads {
                let info = Arc::clone(&info);
                let dual = Arc::clone(&dual);
                let channels = Arc::clone(&channels);
                let phase_barrier = Arc::clone(&phase_barrier);
                let offsets = nodes;
                let neighbors = edges;
                let iterations = Arc::clone(&iterations);
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
                        channels,
                        phase_barrier,
                        offsets,
                        neighbors,
                        iterations,
                        end_iteration,
                        terminate,
                        current_priority,
                        owner,
                        batch_budget,
                        threads_working,
                        edges_processed,
                    )
                });
            }
            // prefill infostore e dual.current
            phase_barrier.wait();
            println!(
                "Inizializzazione finita in {:?}, inizio iterazioni",
                start.elapsed()
            );
            let mut finish: bool = false;
            loop {
                iterations.fetch_add(1, Ordering::Relaxed);

                {
                    if dual.current().lock().is_empty() {
                        // setto terminate a true se current è vuota
                        // le code locali potrebbero contenere nodi residui
                        // si esegue quindi un'ultima iterazione
                        // i thread invocheranno force_merge_from su current
                        // per rimuovere i residui e termineranno l'esecuzione
                        // l'ultimo thread, prima di terminare, processerà
                        // tutti i nodi che rimangono in current, next e le locali
                        // questo avverrebbe alla fine del protocollo, quando
                        // i nodi sono talmente pochi che non conviene più
                        // parallelizzare
                        terminate.store(true, Ordering::Relaxed);
                        end_iteration.store(true, Ordering::Relaxed);
                        finish = true;
                    }
                }
                let batches_in_queue = dual.current().lock().batches_in_queue();
                let mut subiterations = 0;
                current_priority.store(0, Ordering::Relaxed);
                end_iteration.store(false, Ordering::Relaxed);

                phase_barrier.wait();
                loop {
                    subiterations += 1;
                    let p = dual.current().lock().estimate_cutoff_relative(
                        target_batches_per_subiteration,
                        current_priority.load(Ordering::Relaxed),
                    );
                    if dual.current().lock().is_empty() {
                        end_iteration.store(true, Ordering::Relaxed);
                    }
                    current_priority.store(p, Ordering::Relaxed);
                    phase_barrier.wait();
                    // fase 1, estrazione dalla coda condivisa e elaborazione nodi
                    phase_barrier.wait();
                    // fase 2, aggiornamento nodi
                    phase_barrier.wait();
                    // fase 3, invio nodi a cui decrementare stability
                    phase_barrier.wait();
                    // fase 4, ricezione e decremento stability
                    phase_barrier.wait();
                    if end_iteration.load(Ordering::Relaxed) {
                        break;
                    }
                }
                dual.flip();
                println!(
                    "Iterazione {} in {}, batches in coda: {}, tempo dall'inizio: {:?}; Archi processati: {}",
                    iterations.load(Ordering::Relaxed),
                    subiterations,
                    batches_in_queue,
                    start.elapsed(),
                    edges_processed.load(Ordering::Relaxed) as f64
                        / (self.offsets[self.num_nodes] as f64)
                );
                if finish {
                    break;
                }
            }
            phase_barrier.wait();
            phase_barrier.wait();
            println!(
                "Iterazioni: {}, archi processati: {}",
                iterations.load(Ordering::Relaxed),
                edges_processed.load(Ordering::Relaxed) as f64
                    / (self.offsets[self.num_nodes] as f64)
            );
            return iterations.load(Ordering::Relaxed);
        })
    }

    pub fn write_to_file(&self, path: &str) -> io::Result<()> {
        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(path)?;

        for u in self.core.iter() {
            writeln!(file, "{}", u)?;
        }
        Ok(())
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
    let mut graph = Graph::parse_file(in_file);

    println!("Per parsare il file: {:?}", start.elapsed());
    start = Instant::now();
    let iterations = graph.fastk(num_threads, 256);
    println!(
        "Per calcolare coreness con threads in {:?} iterazioni: {:?}",
        iterations,
        start.elapsed()
    );
    graph.write_to_file(&out_file)?;
    // scrittura valori di coreness dei nodi

    Ok(())
}

pub fn thread_routine(
    tid: usize,
    info: Arc<InfoStore>,
    dual: Arc<DualPQShared>,
    channels: Arc<SpscMatrix<usize>>,
    phase_barrier: Arc<Barrier>,
    offsets: &[usize],
    neighbors: &[usize],
    iterations: Arc<AtomicUsize>,
    end_iteration: Arc<AtomicBool>,
    terminate: Arc<AtomicBool>,
    current_priority: Arc<AtomicUsize>,
    owner: OwnerMap,
    batch_budget: BatchBudget,
    threads_working: Arc<AtomicUsize>,
    edges_processed: Arc<AtomicUsize>,
) {
    // inizializzo coda dual locale
    let mut local_queue = DualPQLocal::new(batch_budget);
    let mut count: Vec<u32> = vec![0; 1024];
    // prefilling disgiunto per owner: nessuna barriera necessaria
    let n = info.len();
    let block = owner.block;
    let start_block = tid;
    for v in (start_block * block..n).step_by(owner.num_threads * block) {
        let end = ((v / block) + 1) * block;
        let stop = end.min(n);

        for u in v..stop {
            // owner_of(u) == tid per tutti questi u
            unsafe {
                let node = &mut *info.get(u).get();
                let prio = node.estimate as usize;
                let deg = node.deg as usize;
                if deg > 1 {
                    local_queue.current_mut().push_node(prio, u, deg);
                    node.in_queue = true;
                }
                node.last_active = 0;
            }
        }
    }

    // al termine, un solo merge verso la shared current
    {
        let cur = dual.current();
        let mut q = cur.lock();
        // poni un cutoff molto alto: vogliamo spingere tutti i “pronti”
        q.force_merge_from(local_queue.current_mut());
    }
    phase_barrier.wait(); // barrier inizio iterazioni

    let mut local_updates: Vec<(usize, u32, i32)> = Vec::new();

    let mut last_worker = false;
    let mut finish;

    let mut edges;

    let mut phase1_ns = 0;
    let mut phase2_ns = 0;
    let mut phase3_ns = 0;
    let mut phase4_ns = 0;

    // loop iterazione
    loop {
        edges = 0;
        let mut last_subiter = false;
        phase_barrier.wait();
        finish = terminate.load(Ordering::Relaxed);
        if finish {
            let m = threads_working.fetch_sub(1, Ordering::Relaxed);
            if m == 1 {
                last_worker = true;
            }
        }
        // loop sottoiterazione
        loop {
            phase_barrier.wait(); // barrier inizio sottoiterazioni
            if end_iteration.load(Ordering::Relaxed) {
                last_subiter = true;
            }
            let prio = current_priority.load(Ordering::Relaxed);
            let mut local_prio = prio;
            let iter: u16 = iterations.load(Ordering::Relaxed) as u16;

            if last_subiter {
                local_prio = local_queue.queues.len();
            }

            //==================FASE 1==================
            // estraggo dalla coda locale
            let phase1_start = Instant::now();
            while let Some(batch) = local_queue.current_mut().pop_batch(local_prio) {
                edges += batch.edges;
                for node in batch.nodes {
                    unsafe {
                        let node_info = &mut *info.get(node).get();
                        node_info.in_queue = false;
                        node_info.last_active = iter;
                        let (u, new_estimate, stability) =
                            compute_index(node, &info, offsets, neighbors, &mut count);
                        local_updates.push((u, new_estimate, stability));
                    }
                }
            }
            // estraggo dalla coda condivisa
            loop {
                let batch = { dual.current().lock().pop_batch(prio) };
                if let Some(batch) = batch {
                    edges += batch.edges;
                    for node in batch.nodes {
                        unsafe {
                            let node_info = &mut *info.get(node).get();
                            node_info.in_queue = false;
                            node_info.last_active = iter;
                            let (u, new_estimate, stability) =
                                compute_index(node, &info, offsets, neighbors, &mut count);
                            local_updates.push((u, new_estimate, stability));
                        }
                    }
                } else {
                    break;
                }
            }
            //==========================================
            if last_subiter {
                edges_processed.fetch_add(edges, Ordering::Relaxed);
            }
            phase1_ns += phase1_start.elapsed().as_nanos();
            phase_barrier.wait();

            //==================FASE 2==================
            // aggiorno i nodi e lascio in local_updates
            // (u, new_estimate, old_estimate)
            let phase2_start = Instant::now();
            for i in 0..local_updates.len() {
                unsafe {
                    let (u, new_estimate, stability) = local_updates[i];
                    let node = &mut *info.get(u).get();
                    node.stability = stability;
                    local_updates[i].2 = node.estimate as i32; // ora contiene old_estimate
                    node.estimate = new_estimate;
                }
            }
            phase2_ns += phase2_start.elapsed().as_nanos();
            //==========================================

            phase_barrier.wait();

            //==================FASE 3==================
            // invio nodi a cui decrementare stability
            let phase3_start = Instant::now();
            for (u, new_estimate, old_estimate) in local_updates.drain(..) {
                let neighbors_u = neighbors_slice(offsets, neighbors, u);
                for &v in neighbors_u {
                    unsafe {
                        let node_v = &mut *info.get(v).get();
                        if new_estimate < node_v.estimate && old_estimate as u32 >= node_v.estimate
                        {
                            let owner = owner.owner_of(v);
                            channels.send(tid, owner, v);
                        }
                    }
                }
            }
            phase3_ns += phase3_start.elapsed().as_nanos();
            //==========================================

            phase_barrier.wait();

            //==================FASE 4==================
            // ricezione, decremento stability, inserimento coda locale e merge con condivisa
            let phase4_start = Instant::now();
            for i in 0..owner.num_threads {
                let buf = unsafe { channels.read_from(i, tid) };
                while let Some(v) = buf.pop_front() {
                    unsafe {
                        let node = &mut *info.get(v).get();
                        if node.estimate > 1 {
                            node.stability -= 1;
                            if node.stability < 0 {
                                if node.in_queue {
                                    continue; // già in coda
                                }
                                if node.last_active == iter {
                                    local_queue.next_mut().push_node(
                                        node.estimate as usize,
                                        v,
                                        node.deg as usize,
                                    );
                                } else {
                                    local_queue.current_mut().push_node(
                                        node.estimate as usize,
                                        v,
                                        node.deg as usize,
                                    );
                                }
                                node.in_queue = true;
                            }
                        }
                    }
                }
            }
            // merge current con la coda condivisa
            if last_subiter {
                let cur_should_merge = local_queue.current_mut().need_merge(prio);
                let next_should_merge = local_queue.next_mut().need_merge(prio);
                if cur_should_merge || next_should_merge {
                    let cur = dual.next();
                    let mut q = cur.lock();
                    q.merge_from(local_queue.current_mut(), prio);
                    q.merge_from(local_queue.next_mut(), prio);
                }
                local_queue.merge_to_next();
            } else if local_queue.current_mut().need_merge(prio) {
                let cur = dual.current();
                let mut q = cur.lock();
                q.merge_from(local_queue.current_mut(), prio);
            }

            // se è l'ultima sottoiterazione, faccio un merge forzato di current con next condivisa
            // insieme a un merge normale di next con next condivisa

            //==========================================
            phase4_ns += phase4_start.elapsed().as_nanos();
            phase_barrier.wait();

            // coordinatore fa le sue cose

            if last_subiter {
                println!(
                "Thread {} ha processato in totale {} archi, fase 1: {} ms, fase 2: {} ms, fase 3: {} ms, fase 4: {} ms",
                tid,
                edges,
                phase1_ns / 1_000_000,
                phase2_ns / 1_000_000,
                phase3_ns / 1_000_000,
                phase4_ns / 1_000_000
                );
                phase1_ns = 0;
                phase2_ns = 0;
                phase3_ns = 0;
                phase4_ns = 0;
                break;
            }
        }
        local_queue.flip();

        if finish {
            {
                if !local_queue.current_mut().is_empty() {
                    let cur = dual.current();
                    let mut q = cur.lock();
                    q.force_merge_from(local_queue.current_mut());
                }
                if !local_queue.next_mut().is_empty() {
                    let cur = dual.next();
                    let mut q = cur.lock();
                    q.force_merge_from(local_queue.next_mut());
                }
            }
            break;
        }
    }
    edges_processed.fetch_add(edges, Ordering::Relaxed);

    phase_barrier.wait();
    println!(
        "Thread {} ha processato in totale {} archi, fase 1: {} ms, fase 2: {} ms, fase 3: {} ms, fase 4: {} ms",
        tid,
        edges,
        phase1_ns / 1_000_000,
        phase2_ns / 1_000_000,
        phase3_ns / 1_000_000,
        phase4_ns / 1_000_000
    );
    // barrier fine iterazioni
    if last_worker {
        let p = dual.current();
        let q = dual.next();
        let mut queue = p.lock();
        let mut next = q.lock();
        queue.force_merge_from(&mut next); // tutti i nodi residui sono in questa coda

        let batches_ready = queue.buckets.iter().fold(0, |acc, x| acc + x.len());
        println!("Sono rimasti {} batch residui in tutto", batches_ready);

        let nodes_left: usize = queue
            .buckets
            .iter()
            .map(|b| b.iter().map(|batch| batch.len()).sum::<usize>())
            .sum();
        println!("Sono rimasti {} nodi residui in tutto", nodes_left);
        // algoritmo sequenziale

        // l'ultimo thread finisce di elaborare tutti i nodi sequenzialmente:
        // tutte le code locali devono essere mergeate con quella condivisa
    }

    phase_barrier.wait();
}

#[inline(always)]
pub fn compute_index(
    u: usize,
    nodes: &InfoStore,
    offsets: &[usize],
    neighbors: &[usize],
    count: &mut Vec<u32>,
) -> (usize, u32, i32) {
    unsafe {
        let node = &mut *nodes.get(u).get();
        let k = node.estimate;
        if k >= count.len() as u32 {
            count.resize(k as usize + 1, 0);
        }

        count[..=k as usize].fill(0);

        let mut index;
        for neighbor in neighbors_slice(offsets, neighbors, u) {
            let neighbor_node = &mut *nodes.get(*neighbor).get();
            let neighbor_est = neighbor_node.estimate;
            if neighbor_est > k {
                index = k;
            } else {
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

        (u, i as u32, stability)
    }
}
