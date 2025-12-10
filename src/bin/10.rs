#![allow(dead_code)]
use std::collections::HashSet;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::BufReader;
use std::io::{self, BufRead, Write};
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::sync::Barrier;
use std::thread;
use std::time::Instant;

const THRESHOLD_OPTIMIZATION_1: usize = 5;
const THRESHOLD_OPTIMIZATION_2: usize = 5;

pub struct Graph {
    pub num_nodes: usize,
    pub offsets: Vec<usize>,
    pub neighbors: Vec<usize>,
    pub core: Vec<usize>,
    pub avg_deg: usize,
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
        for i in 0..num_nodes {
            offsets[i + 1] = offsets[i] + degree[i];
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
        let total_degree: usize = degree.iter().sum();
        let avg_deg: usize = total_degree / num_nodes;

        Graph {
            num_nodes,
            offsets,
            neighbors,
            core: Vec::from_iter((0..num_nodes).map(|_| 0)), // inizializza core a zero
            avg_deg: avg_deg,
        }
    }

    #[inline(always)]
    pub fn neighbors_of(&self, u: usize) -> &[usize] {
        let start = self.offsets[u];
        let end = self.offsets[u + 1];
        &self.neighbors[start..end]
    }

    pub fn degree_of(&self, u: usize) -> usize {
        self.offsets[u + 1] - self.offsets[u]
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

    pub fn print_info(&self) {
        println!("Numero di nodi: {}", self.num_nodes);
        println!("Numero di archi: {}", self.offsets[self.num_nodes] / 2);
        // Controllo che il numero di archi sia corretto
        for i in 0..self.num_nodes {
            let degree = self.degree_of(i);
            if degree != self.neighbors_of(i).len() {
                println!("Errore nel calcolo del grado per il nodo {}", i);
            }
        }
        // controllo che non ci siano duplicati in ogni lista di vicini
        let mut seen = HashSet::new();
        let mut number_of_duplicates = 0;
        for i in 0..self.num_nodes {
            seen.clear();
            for &neighbor in self.neighbors_of(i) {
                if seen.contains(&neighbor) {
                    number_of_duplicates += 1;
                } else {
                    seen.insert(neighbor);
                }
            }
        }
        println!("Numero di duplicati: {}", number_of_duplicates);
        println!(
            "Numero di archi vero: {}",
            self.offsets[self.num_nodes] / 2 - number_of_duplicates
        );
    }

    pub fn compute_coreness_threads(&mut self, num_threads: usize, chunk_size: usize) -> usize {
        let n = self.num_nodes;

        assert_eq!(self.offsets.len(), self.num_nodes + 1);

        let mut est = vec![0; n];
        let mut active = vec![true; n];

        for i in 0..(n) {
            let d = self.degree_of(i);
            est[i] = d;
            self.core[i] = d;
        }

        let core_addr = Arc::new(self.core.as_mut_ptr() as usize);
        let est_addr = Arc::new(est.as_mut_ptr() as usize);
        let active_addr = Arc::new(active.as_mut_ptr() as usize);

        // puntatori statici a offsets e neighbors
        let offsets_ptr = Arc::new(self.offsets.as_ptr() as usize);
        let neighbors_ptr = Arc::new(self.neighbors.as_ptr() as usize);

        let index = Arc::new(AtomicUsize::new(0));
        let changed = Arc::new(AtomicBool::new(false));
        let barrier = Arc::new(Barrier::new(num_threads + 1));

        let mut iterations = 0;

        thread::scope(|s| {
            for _ in 0..num_threads {
                let index = Arc::clone(&index);
                let changed = Arc::clone(&changed);
                let barrier = Arc::clone(&barrier);
                let est_addr = Arc::clone(&est_addr);
                let core_addr = Arc::clone(&core_addr);
                let active_addr = Arc::clone(&active_addr);

                // passaggio dei raw pointer
                let offsets_addr = Arc::clone(&offsets_ptr);
                let neighbors_addr = Arc::clone(&neighbors_ptr);

                s.spawn(move || {
                    let mut local_updates = Vec::new();
                    let mut local_activated = Vec::new();
                    let mut count: Vec<usize> = vec![0; 1024];
                    let chunk_count = (n + chunk_size - 1) / chunk_size;

                    let mut count_ptr = count.as_mut_ptr();
                    let mut count_len = count.capacity();
                    let est_ptr = *est_addr as *mut usize;
                    let active_ptr = *active_addr as *mut bool;
                    let core_ptr = *core_addr as *mut usize;

                    let offsets_ptr = *offsets_addr as *const usize;
                    let neighbors_ptr = *neighbors_addr as *const usize;

                    loop {
                        let mut local_changed = false;
                        barrier.wait();

                        local_updates.clear();
                        local_activated.clear();

                        loop {
                            let i = index.fetch_add(1, Ordering::Relaxed);
                            if i >= chunk_count {
                                break;
                            }

                            let start = i * chunk_size;
                            let mut end = start + chunk_size;
                            if end > n {
                                end = n;
                            }

                            unsafe {
                                for u in start..end {
                                    if !*active_ptr.add(u) {
                                        continue;
                                    }
                                    *active_ptr.add(u) = false;
                                    let old_coreness = *core_ptr.add(u);

                                    let k = *est_ptr.add(u);
                                    if k > count_len - 1 {
                                        // se count_len è troppo piccolo, lo aumento
                                        count_len = k + 1;
                                        count.resize(count_len, 0);
                                        count_ptr = count.as_mut_ptr();
                                    }
                                    let max = k.min(count_len - 1);
                                    for i in 0..=max {
                                        *count_ptr.add(i) = 0;
                                    }

                                    let neighbors = raw_neighbors_of(offsets_ptr, neighbors_ptr, u);
                                    for &v in neighbors {
                                        let est_v = *est_ptr.add(v);
                                        let min_val = est_v.min(k);
                                        *count_ptr.add(min_val) += 1;
                                    }

                                    let mut new_k = 0;

                                    // accumulo inverso e trova nuovo k
                                    let mut i = max;
                                    while i > 0 {
                                        let count_i = *count_ptr.add(i);
                                        if count_i >= i {
                                            new_k = i;
                                            break;
                                        }
                                        *count_ptr.add(i - 1) += count_i;
                                        i -= 1;
                                    }

                                    *core_ptr.add(u) = new_k;

                                    if new_k != old_coreness {
                                        local_updates.push((u, new_k));
                                        local_changed = true;

                                        for &v in neighbors {
                                            if *est_ptr.add(v) > new_k {
                                                local_activated.push((v, old_coreness));
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        changed.fetch_or(local_changed, Ordering::Relaxed);
                        barrier.wait();

                        unsafe {
                            for (id, new_core) in &local_updates {
                                *est_ptr.add(*id) = *new_core;
                            }

                            for &(v, _) in &local_activated {
                                *active_ptr.add(v) = true;
                            }

                            barrier.wait();
                        }

                        let finish = !changed.load(Ordering::Relaxed);
                        barrier.wait();
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
                barrier.wait();
                barrier.wait();
                barrier.wait();
                barrier.wait();
                if !changed.load(Ordering::Relaxed) {
                    break;
                }
            }
        });
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
    let mut start = Instant::now();
    let mut graph = Graph::parse_file(in_file);

    println!("Per parsare il file: {:?}", start.elapsed());
    start = Instant::now();
    let iterations = graph.compute_coreness_threads(12, 256);
    println!(
        "Per calcolare coreness con threads in {:?} iterazioni: {:?}",
        iterations,
        start.elapsed()
    );
    graph.write_to_file(&out_file)?;
    // scrittura valori di coreness dei nodi

    Ok(())
}

#[inline(always)]
// prende i puntatori a offset e neighbors e restituisce la lista di vicini di un nodo
unsafe fn raw_neighbors_of<'a>(
    offsets: *const usize,
    neighbors: *const usize,
    node_id: usize,
) -> &'a [usize] {
    let start = *offsets.add(node_id);
    let end = *offsets.add(node_id + 1);
    let ptr = neighbors.add(start);
    std::slice::from_raw_parts(ptr, end - start)
}
