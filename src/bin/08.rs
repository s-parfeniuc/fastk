#![allow(dead_code)]
use crossbeam::queue::SegQueue;
use rayon::iter::IntoParallelRefMutIterator;
use rayon::iter::ParallelIterator;
use std::cmp;
use std::collections::HashSet;
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::sync::Condvar;
use std::sync::Mutex;
use std::thread;
use std::time::Instant;
use std::usize::MAX;
/*
Utilizzo di AtomicUsize: i nodi non hanno più una coda di messaggi e accedono direttamente ai valori di coreness dei vicini. In più introdotta una priority
con livelli diversi di priorità in base al numero di coreness
*/

pub struct ChunkPriorityQueue {
    queues: Vec<Arc<SegQueue<usize>>>, // ogni priorità ha una queue di indici
    k_max: usize,
}

impl ChunkPriorityQueue {
    pub fn new(k_max: usize) -> Self {
        let queues = (0..=k_max).map(|_| Arc::new(SegQueue::new())).collect();
        Self { queues, k_max }
    }

    pub fn push(&self, coreness: usize, index: usize) {
        assert!(
            coreness <= self.k_max,
            "coreness oltre il massimo consentito"
        );
        self.queues[coreness].push(index);
    }

    pub fn pop_chunk(&self, chunk_size: usize) -> Option<Vec<usize>> {
        for queue in &self.queues {
            if !queue.is_empty() {
                let mut chunk = Vec::with_capacity(chunk_size);
                for _ in 0..chunk_size {
                    if let Some(val) = queue.pop() {
                        chunk.push(val);
                    } else {
                        break;
                    }
                }
                if !chunk.is_empty() {
                    return Some(chunk);
                }
            }
        }
        None
    }

    pub fn is_empty(&self) -> bool {
        self.queues.iter().all(|q| q.is_empty())
    }
}

struct Node {
    id: usize,
    coreness: Arc<AtomicUsize>,
    neighbors: Vec<(usize, Arc<AtomicUsize>, Arc<AtomicBool>)>, // lista di vicini,
    changed: bool, // indica se è stato cambiato dall'ultima fase di invio messaggi
    message: Arc<AtomicBool>, // indica se è cambiato uno dei suoi vicini
}

impl Node {
    pub fn new(n: usize) -> Self {
        Node {
            id: n,
            coreness: Arc::new(AtomicUsize::new(MAX)),
            neighbors: Vec::new(),
            changed: true,
            message: Arc::new(AtomicBool::new(true)),
        }
    }

    pub fn add_neighbor(&mut self, node: Arc<AtomicUsize>, message: Arc<AtomicBool>, id: usize) {
        // aggiunge un nuovo vicino
        self.neighbors.push((id, node, message));
    }

    pub fn init(&mut self) {
        // elimina duplicati, se presenti, dalla lista di vicini
        let mut seen: HashSet<usize> = HashSet::new();

        // usa un HashSet per vedere se gli elementi sono già stati "visti"
        self.neighbors.retain(|x| {
            let id = x.0;
            seen.insert(id) // il metodo restituisce true se l'id non è stato ancora inserito
        });

        // inizializza la propria coreness con la lunghezza della lista di adiacenza
        self.coreness.store(self.neighbors.len(), Ordering::SeqCst);

        // invia un messaggio a tutti i vicini
        self.changed = true;
        self.message.store(true, Ordering::Relaxed);
        self.send_messages();
    }

    pub fn compute_index(&mut self, queue: &Arc<ChunkPriorityQueue>) -> usize {
        self.message.store(false, Ordering::SeqCst);
        let core = self.coreness.load(Ordering::SeqCst);

        self.changed = false;

        if core == 0 {
            return 0;
        }

        let mut count: Vec<usize> = Vec::with_capacity(core + 1);
        count.resize(core + 1, 0);

        let mut neighbor_estimates = Vec::new();

        for neighbor in self.neighbors.iter() {
            let v2 = neighbor.1.load(Ordering::Acquire);

            neighbor_estimates.push((neighbor.0, v2));

            let k = cmp::min(core, v2);
            count[k] += 1;
        }

        for i in (1..core + 1).rev() {
            count[i - 1] += count[i];
        }

        let mut i = core;
        while i > 1 && count[i] < i {
            i -= 1;
        }
        if i < core {
            for neighbor_id in 0..neighbor_estimates.len() {
                if i < neighbor_estimates[neighbor_id].1 {
                    self.neighbors[neighbor_id].2.store(true, Ordering::Relaxed);
                    queue.push(
                        neighbor_estimates[neighbor_id].1,
                        neighbor_estimates[neighbor_id].0,
                    );
                }
            }
            self.changed = true;
        }

        self.coreness.store(i, Ordering::SeqCst);

        return i;
    }

    pub fn send_messages(&mut self) -> bool {
        if self.changed {
            self.changed = false;
            for neighbor in &mut self.neighbors {
                neighbor.2.store(true, Ordering::SeqCst);
            }
            return true;
        }
        false
    }
}

struct Graph {
    inmap: Vec<Node>,
}

impl Graph {
    pub fn new() -> Self {
        Graph { inmap: Vec::new() }
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
        let coreness_i = Arc::clone(&self.inmap[i].coreness);
        let coreness_j = Arc::clone(&self.inmap[j].coreness);

        let message_i = Arc::clone(&self.inmap[i].message);
        let message_j = Arc::clone(&self.inmap[j].message);

        self.inmap[i].add_neighbor(coreness_j, message_j, j);
        self.inmap[j].add_neighbor(coreness_i, message_i, i);
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

    // metodo che scrive su un file il valore di coreness di ciascun nodo
    pub fn write_to_file(&self, filename: &str) -> std::io::Result<()> {
        let mut file = File::create(filename)?;
        for n in &self.inmap {
            writeln!(file, "{}", n.coreness.load(Ordering::SeqCst))?;
        }

        Ok(())
    }

    pub fn compute_coreness_threads(&mut self, num_threads: usize, chunk_size: usize) {
        let inmap_len = self.inmap.len();
        let inmap_base = self.inmap.as_ptr() as usize;
        let inmap_base = Arc::new(inmap_base);

        let k_max = self
            .inmap
            .iter()
            .map(|x| x.coreness.load(Ordering::Relaxed))
            .max()
            .unwrap();

        let queue = Arc::new(ChunkPriorityQueue::new(k_max));

        // Inserisci tutti i nodi iniziali nella priorità massima
        for i in 0..inmap_len {
            queue.push(k_max, i);
        }

        let active_threads = Arc::new(AtomicUsize::new(num_threads));
        let condvar_pair = Arc::new((Mutex::new(()), Condvar::new()));

        thread::scope(|s| {
            for _ in 0..num_threads {
                let queue = Arc::clone(&queue);
                let inmap_base = Arc::clone(&inmap_base);
                let active_threads = Arc::clone(&active_threads);
                let condvar_pair = Arc::clone(&condvar_pair);

                s.spawn(move || {
                    'worker: loop {
                        match queue.pop_chunk(chunk_size) {
                            Some(chunk) => {
                                let base_ptr = *inmap_base as *const Node;
                                for i in chunk {
                                    unsafe {
                                        let node = &mut *(base_ptr.add(i) as *mut Node);
                                        let _new_coreness = node.compute_index(&queue);
                                    }
                                    condvar_pair.1.notify_all();
                                }
                            }

                            None => {
                                let prev = active_threads.fetch_sub(1, Ordering::SeqCst);
                                if prev == 1 {
                                    condvar_pair.1.notify_all(); // ultimo thread notifica chi è in attesa
                                    break;
                                }

                                let (lock, cvar) = &*condvar_pair;
                                let mut guard = lock.lock().unwrap();

                                // Attende finché c'è nuova attività o tutto è davvero finito
                                loop {
                                    if !queue.is_empty() {
                                        drop(guard);
                                        active_threads.fetch_add(1, Ordering::SeqCst);
                                        break;
                                    }

                                    if active_threads.load(Ordering::SeqCst) == 0 {
                                        drop(guard);
                                        break 'worker;
                                    }

                                    guard = cvar.wait(guard).unwrap();
                                }
                            }
                        }
                    }
                });
            }
        });
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

    // inizializza le variabili necessarie per l'algoritmo
    start = Instant::now();
    graph.init_graph();
    println!("Per inizializzare i nodi: {:?}", start.elapsed());

    start = Instant::now();
    graph.compute_coreness_threads(3, 64);
    println!("Per calcolare coreness con threads: {:?}", start.elapsed());

    // scrittura valori di coreness dei nodi
    graph.write_to_file(&out_file)?;

    Ok(())
}
