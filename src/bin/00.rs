#![allow(dead_code)]
use rayon::iter::IntoParallelRefMutIterator;
use rayon::iter::ParallelIterator;
use std::cmp;
use std::collections::VecDeque;
use std::fs::File;
use std::io::BufWriter;
use std::io::{self, BufRead, Write};
use std::slice;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::sync::Barrier;
use std::thread;
use std::time::Instant;

struct Node {
    id: usize,
    neighbors: Vec<usize>, // lista di indici dei vicini,
    coreness: usize,
}

impl Node {
    pub fn new(n: usize) -> Self {
        Node {
            id: n,
            neighbors: Vec::new(),
            coreness: 0,
        }
    }

    pub fn add_neighbor(&mut self, id: usize) {
        // aggiunge un nuovo vicino
        self.neighbors.push(id);
    }

    pub fn init(&mut self) {
        // elimina duplicati, se presenti, dalla lista di vicini
        self.neighbors.sort();
        let mut j = 0;
        for i in 1..self.neighbors.len() {
            if self.neighbors[i] != self.neighbors[j] {
                j += 1;
                self.neighbors[j] = self.neighbors[i];
            }
        }
        self.neighbors.truncate(j + 1);
        self.coreness = self.neighbors.len();
    }

    pub fn compute_index(&mut self, est: *const usize) -> bool {
        let core = self.coreness;
        if core == 0 {
            return false;
        }

        let mut count: Vec<usize> = Vec::with_capacity(core + 1);
        count.resize(core + 1, 0);
        unsafe {
            for neighbor in &self.neighbors {
                let k = cmp::min(core, *est.add(*neighbor));
                count[k] += 1;
            }
        }

        for i in (1..core + 1).rev() {
            count[i - 1] += count[i];
        }

        let mut i = core;
        while i > 1 && count[i] < i {
            i -= 1;
        }
        if self.coreness > i {
            self.coreness = i;
            return true;
        }
        return false;
    }
}

pub struct Queue {
    queues: Vec<VecDeque<usize>>,
}

impl Queue {
    pub fn new(max_k: usize) -> Self {
        let mut queues = Vec::with_capacity(max_k + 1);
        for _ in 0..=max_k {
            queues.push(VecDeque::new());
        }
        Self { queues }
    }

    /// Inserisce un elemento `value` nella coda di priorità `k`
    pub fn push(&mut self, k: usize, value: usize) {
        if k < self.queues.len() {
            self.queues[k].push_back(value);
        } else {
            for _ in self.queues.len()..k {
                self.queues.push(VecDeque::new());
            }
            self.queues[k].push_back(value);
        }
    }

    /// Estrae il primo elemento disponibile dalla coda di priorità più alta (cioè dal primo indice non vuoto)
    pub fn pop(&mut self) -> Option<usize> {
        for queue in &mut self.queues {
            if let Some(value) = queue.pop_front() {
                return Some(value);
            }
        }
        None
    }

    /// Controlla se tutte le code sono vuote
    pub fn is_empty(&self) -> bool {
        self.queues.iter().all(|q| q.is_empty())
    }
}

struct Graph {
    inmap: Vec<Node>,
}

impl Graph {
    pub fn new() -> Self {
        Graph { inmap: Vec::new() }
    }

    pub fn print_info(&self) {
        println!(
            "Numero di nodi: {}, Numero di archi: {}",
            self.inmap.len(),
            self.inmap.iter().map(|x| x.neighbors.len()).sum::<usize>() / 2,
        );
    }

    pub fn add_edge(&mut self, i: usize, j: usize) {
        if i >= self.inmap.len() || j >= self.inmap.len() {
            let old_len = self.inmap.len();
            let new_len = cmp::max(i, j) + 1;
            for n in old_len..new_len {
                self.inmap.push(Node::new(n));
            }
        }
        if i == j {
            return;
        }

        self.inmap[i].add_neighbor(j);
        self.inmap[j].add_neighbor(i);
    }

    // inizializza tutti i nodi con i valori opportuni, chiamata dopo aver aggiunto tutti i nodi
    pub fn init_graph(&mut self) {
        self.inmap.par_iter_mut().for_each(|x| {
            x.init();
        });
    }

    // crea un grafo a partire da un file ignorando righe che iniziano con #
    pub fn parse_file(&mut self, filename: &str) -> std::io::Result<()> {
        let file = File::open(filename)?;
        let reader = io::BufReader::new(file);
        for line in reader.lines() {
            let line = line?;
            if line.starts_with('#') {
                continue;
            }
            let numbers: Vec<usize> = line
                .split_whitespace()
                .filter_map(|s| s.parse().ok())
                .collect();

            if numbers.len() == 2 {
                let _ = self.add_edge(numbers[0], numbers[1]);
            } else {
                println!("Skipping invalid line: {}", line);
            }
        }
        Ok(())
    }

    pub fn write_edges_undirected(&self, path: &str) -> io::Result<()> {
        let file = File::create(path)?;
        let mut writer = BufWriter::new(file);

        for node in &self.inmap {
            let u = node.id;
            for &v in &node.neighbors {
                if u < v {
                    writeln!(writer, "{} {}", u, v)?;
                }
            }
        }

        Ok(())
    }

    // metodo che scrive su un file il valore di coreness di ciascun nodo
    pub fn write_to_file(&self, filename: &str) -> std::io::Result<()> {
        let mut file = File::create(filename)?;
        for n in &self.inmap {
            writeln!(file, "{}", n.coreness)?;
        }

        Ok(())
    }

    pub fn compute_coreness_threads(&mut self, num_threads: usize, chunk_size: usize) -> usize {
        let n = self.inmap.len();

        let start = Instant::now();
        // est e active persistenti
        let mut est = vec![0; n];
        for node in &self.inmap {
            est[node.id] = node.coreness;
        }
        println!(
            "Tempo per inizializzare est sequenzialmente: {:?}",
            start.elapsed()
        );
        let mut active = vec![true; n];

        let est_addr = Arc::new(est.as_mut_ptr() as usize);
        let active_addr = Arc::new(active.as_mut_ptr() as usize);

        // Chunk come (ptr_addr, len)
        let chunks: Vec<(usize, usize)> = self
            .inmap
            .chunks_mut(chunk_size)
            .map(|chunk| (chunk.as_mut_ptr() as usize, chunk.len()))
            .collect();
        let chunk_count = chunks.len();
        let chunks = Arc::new(chunks);

        let index = Arc::new(AtomicUsize::new(0));
        let changed = Arc::new(AtomicBool::new(false));
        let barrier = Arc::new(Barrier::new(num_threads + 1));

        let mut iterations = 0;

        thread::scope(|s| {
            for _ in 0..num_threads {
                let index = Arc::clone(&index);
                let changed = Arc::clone(&changed);
                let chunks = Arc::clone(&chunks);
                let est_addr = Arc::clone(&est_addr);
                let active_addr = Arc::clone(&active_addr);
                let barrier = Arc::clone(&barrier);

                s.spawn(move || {
                    let mut local_updates = Vec::new();
                    let mut local_activated = Vec::new();

                    loop {
                        let mut local_changed = false;
                        barrier.wait(); // inizio iterazione

                        local_updates.clear();
                        local_activated.clear();
                        let est_ptr = *est_addr as *const usize;
                        let active_ptr = *active_addr as *mut bool;

                        // Fase 1: lettura e calcolo
                        loop {
                            let i = index.fetch_add(1, Ordering::Relaxed);
                            if i >= chunk_count {
                                break;
                            }

                            let (addr, len) = chunks[i];
                            let ptr = addr as *mut Node;
                            unsafe {
                                let chunk = slice::from_raw_parts_mut(ptr, len);
                                for node in chunk.iter_mut() {
                                    // accesso diretto a active[node.id]
                                    let active_flag = active_ptr.add(node.id);
                                    if !*active_flag {
                                        continue;
                                    }
                                    *active_flag = false;
                                    let old_coreness = node.coreness;
                                    if node.compute_index(est_ptr) {
                                        local_updates.push((node.id, node.coreness));
                                        local_changed = true;

                                        // Attiva i vicini con coreness maggiore
                                        for &neighbor_id in &node.neighbors {
                                            if *est_ptr.add(neighbor_id) > node.coreness {
                                                local_activated.push((neighbor_id, old_coreness));
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        changed.fetch_or(local_changed, Ordering::Relaxed);
                        barrier.wait(); // fine compute

                        // Fase 2: scrittura
                        unsafe {
                            let est_ptr = *est_addr as *mut usize;
                            let active_ptr = *active_addr as *mut bool;

                            for (id, new_core) in &local_updates {
                                *est_ptr.add(*id) = *new_core;
                            }
                            for &id in &local_activated {
                                *active_ptr.add(id.0) = true;
                            }
                        }

                        let finish = !changed.load(Ordering::Relaxed);
                        barrier.wait(); // fine iterazione
                        if finish {
                            break;
                        }
                    }
                });
            }

            // Coordinatore principale
            loop {
                iterations += 1;
                changed.store(false, Ordering::Relaxed);
                index.store(0, Ordering::Relaxed);

                barrier.wait(); // inizio iterazione
                barrier.wait(); // dopo compute
                barrier.wait(); // dopo scrittura

                if !changed.load(Ordering::Relaxed) {
                    break;
                }
            }
        });

        iterations
    }

    pub fn compute_coreness_threads_hybrid(
        &mut self,
        num_threads: usize,
        chunk_size: usize,
    ) -> usize {
        let n = self.inmap.len();

        let soglia = (chunk_size) as usize;
        // est e active persistenti
        let mut est = vec![0; n];
        for node in &self.inmap {
            est[node.id] = node.coreness;
        }
        let mut active = vec![true; n];

        let est_addr = Arc::new(est.as_mut_ptr() as usize);
        let active_addr = Arc::new(active.as_mut_ptr() as usize);

        // Chunk come (ptr_addr, len)
        let chunks: Vec<(usize, usize)> = self
            .inmap
            .chunks_mut(chunk_size)
            .map(|chunk| (chunk.as_mut_ptr() as usize, chunk.len()))
            .collect();
        let chunk_count = chunks.len();
        let chunks = Arc::new(chunks);

        let index = Arc::new(AtomicUsize::new(0));
        let changed = Arc::new(AtomicBool::new(false));
        let barrier = Arc::new(Barrier::new(num_threads + 1));

        let number_changed = Arc::new(AtomicUsize::new(0));

        let mut iterations = 0;

        thread::scope(|s| {
            for _ in 0..num_threads {
                let index = Arc::clone(&index);
                let changed = Arc::clone(&changed);
                let chunks = Arc::clone(&chunks);
                let est_addr = Arc::clone(&est_addr);
                let active_addr = Arc::clone(&active_addr);
                let barrier = Arc::clone(&barrier);
                let num_changed = Arc::clone(&number_changed);

                s.spawn(move || {
                    let mut local_updates = Vec::new();
                    let mut local_activated = Vec::new();
                    let mut iterations = 0;

                    loop {
                        iterations += 1;
                        let mut local_changed = false;
                        barrier.wait(); // inizio iterazione

                        local_updates.clear();
                        local_activated.clear();
                        let est_ptr = *est_addr as *const usize;
                        let active_ptr = *active_addr as *mut bool;

                        // Fase 1: lettura e calcolo
                        loop {
                            let i = index.fetch_add(1, Ordering::Relaxed);
                            if i >= chunk_count {
                                break;
                            }

                            let (addr, len) = chunks[i];
                            let ptr = addr as *mut Node;
                            unsafe {
                                let chunk = slice::from_raw_parts_mut(ptr, len);
                                for node in chunk.iter_mut() {
                                    // accesso diretto a active[node.id]
                                    let active_flag = active_ptr.add(node.id);
                                    if !*active_flag {
                                        continue;
                                    }
                                    *active_flag = false;
                                    let old_coreness = node.coreness;
                                    if node.compute_index(est_ptr) {
                                        local_updates.push((node.id, node.coreness));
                                        local_changed = true;

                                        // Attiva i vicini con coreness maggiore
                                        for &neighbor_id in &node.neighbors {
                                            if *est_ptr.add(neighbor_id) > node.coreness {
                                                local_activated.push((neighbor_id, old_coreness));
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        changed.fetch_or(local_changed, Ordering::Relaxed);
                        barrier.wait(); // fine compute

                        num_changed.fetch_add(local_updates.len(), Ordering::Relaxed);
                        // Fase 2: scrittura
                        unsafe {
                            let est_ptr = *est_addr as *mut usize;
                            let active_ptr = *active_addr as *mut bool;

                            for (id, new_core) in &local_updates {
                                *est_ptr.add(*id) = *new_core;
                            }
                            for &id in &local_activated {
                                *active_ptr.add(id.0) = true;
                            }
                        }
                        if iterations % 5 == 0 {
                            barrier.wait();
                            barrier.wait();
                        }

                        let finish = !changed.load(Ordering::Relaxed);
                        barrier.wait(); // fine iterazione
                        if finish {
                            break;
                        }
                    }
                });
            }

            // Coordinatore principale
            loop {
                iterations += 1;
                changed.store(false, Ordering::Relaxed);
                index.store(0, Ordering::Relaxed);
                number_changed.store(0, Ordering::Relaxed);

                barrier.wait(); // inizio iterazione
                barrier.wait(); // dopo compute
                barrier.wait(); // dopo scrittura
                if iterations % 5 == 0 {
                    let active_nodes = number_changed.load(Ordering::Relaxed);

                    if active_nodes < soglia {
                        changed.store(false, Ordering::Relaxed);
                    }
                    barrier.wait();
                    barrier.wait();
                }

                if !changed.load(Ordering::Relaxed) {
                    break;
                }
            }
        });
        // fase sequenziale

        let mut queue = Queue::new(10);

        // Inserisci i nodi ancora attivi nella coda con priorità log2(est)
        for node_id in 0..n {
            if active[node_id] {
                let node = &mut self.inmap[node_id];
                let old_est = est[node_id];
                active[node_id] = false;
                // Usa compute_index con est attuale
                if node.compute_index(est.as_ptr()) {
                    let new_est = node.coreness;
                    est[node_id] = new_est;

                    for &neighbor_id in &node.neighbors {
                        if !active[neighbor_id]
                            && est[neighbor_id] > new_est
                            && old_est >= est[neighbor_id]
                        {
                            active[neighbor_id] = true;
                            let priority = (est[neighbor_id].max(1) as f64).log2().floor() as usize;
                            queue.push(priority, neighbor_id);
                        }
                    }
                }
            }
        }

        while !queue.is_empty() {
            if let Some(node_id) = queue.pop() {
                let node = &mut self.inmap[node_id];
                let old_est = est[node_id];
                active[node_id] = false;
                // Usa compute_index con est attuale
                if node.compute_index(est.as_ptr()) {
                    let new_est = node.coreness;
                    est[node_id] = new_est;

                    for &neighbor_id in &node.neighbors {
                        if !active[neighbor_id]
                            && est[neighbor_id] > new_est
                            && old_est >= est[neighbor_id]
                        {
                            active[neighbor_id] = true;
                            let priority = (est[neighbor_id].max(1) as f64).log2().floor() as usize;
                            queue.push(priority, neighbor_id);
                        }
                    }
                }
            }
        }
        iterations
    }
}

fn main() -> std::io::Result<()> {
    // gestione argomenti passati da linea di comando: in_file (file da parsare) e out_file (file su cui scrivere la coreness dei nodi)
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        println!("2 argomenti: file di input e file in cui scrivere");
        return Ok(());
    }
    let in_file = &args[1];
    let out_file = &args[2];

    let mut graph = Graph::new();

    let mut start = Instant::now();

    // crea il grafo a partire dal file
    graph.parse_file(in_file)?;
    println!("Per parsare il file: {:?}", start.elapsed());

    graph.init_graph();
    start = Instant::now();
    graph.print_info();
    graph.compute_coreness_threads(12, 128);
    println!("Per calcolare coreness con threads: {:?}", start.elapsed());

    let mut coreness = Vec::new();
    for node in graph.inmap.iter() {
        coreness.push(node.coreness);
    }
    graph.init_graph();
    start = Instant::now();
    graph.compute_coreness_threads_hybrid(12, 128);
    println!("Per calcolare coreness con threads: {:?}", start.elapsed());
    // scrittura valori di coreness dei nodi
    graph.write_to_file(&out_file)?;

    Ok(())
}

#[test]
fn test() {
    use std::fs::OpenOptions;
    let graphs: [&str; 10] = [
        "web-Stanford",
        "web-BerkStan",
        "web-Google",
        "web-NotreDame",
        "wiki-Talk",
        "soc-pokec-relationships",
        "soc-LiveJournal1",
        "roadNet-CA",
        "roadNet-PA",
        "roadNet-TX",
    ];

    let data_file = "./data/progress_data.csv";

    let batch_sizes: [usize; 1] = [256];

    let nums_threads: [usize; 1] = [16];

    // apro file in append mode
    let mut file = OpenOptions::new()
        .write(true)
        .append(true)
        .open(data_file)
        .unwrap();

    for graph_name in graphs {
        let file_name = "./graphs/".to_owned() + graph_name + "/" + graph_name + ".txt";
        let mut graph = Graph::new();

        let _m = graph.parse_file(&file_name);

        for num_threads in nums_threads {
            for chunk_size in batch_sizes {
                for _ in 0..5 {
                    graph.init_graph();
                    let start = Instant::now();
                    let iter = graph.compute_coreness_threads_hybrid(num_threads, chunk_size);

                    let data = "fastK".to_owned()
                        + ","
                        + graph_name
                        + ","
                        + format!("{:?}", start.elapsed()).as_str()
                        + ","
                        + chunk_size.to_string().as_str()
                        + ","
                        + num_threads.to_string().as_str()
                        + ","
                        + iter.to_string().as_str()
                        + "\n";
                    let _n = file.write_all(data.as_bytes());
                }
            }
        }
    }
}
