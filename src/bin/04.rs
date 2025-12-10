#![allow(dead_code)]
use rayon::iter::IntoParallelRefMutIterator;
use rayon::iter::ParallelIterator;
use std::cmp;
use std::collections::{HashSet, VecDeque};
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::sync::Barrier;
use std::sync::RwLock;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;
use std::usize::MAX;
/*
Ogni iterazione non è più divisa in 2 fasi (calcolo coreness e invio messaggi); le 2 fasi sono unite in modo da dover iterare il vettore dei nodi
una sola volta. Il numero di iterazioni non è più deterministico e in media è ridotto del 30% (di conseguenza anche il runtime).
*/

struct Estimates {
    est: Vec<(usize, usize)>,
}
impl Estimates {
    pub fn new() -> Self {
        Self { est: Vec::new() }
    }

    pub fn push(&mut self, value: (usize, usize)) {
        self.est.push(value);
    }

    pub fn init(&mut self) {
        self.est.sort_by_key(|&(a, _b)| a);
    }

    pub fn insert(&mut self, key: usize, value: usize) {
        let index = self.est.binary_search_by_key(&key, |&(a, _b)| a).unwrap();
        self.est[index].1 = value;
    }

    pub fn get(&mut self, key: usize) -> usize {
        let index = self.est.binary_search_by_key(&key, |&(a, _b)| a).unwrap();
        self.est[index].1
    }
}
struct MessageMail {
    id: usize,
    messages: VecDeque<(usize, usize)>,
}

impl MessageMail {
    pub fn new(n: usize) -> Self {
        Self {
            id: n,
            messages: VecDeque::new(),
        }
    }

    pub fn push(&mut self, message: (usize, usize)) {
        self.messages.push_back(message);
    }

    pub fn pop(&mut self) -> Option<(usize, usize)> {
        self.messages.pop_front()
    }

    pub fn is_empty(&self) -> bool {
        self.messages.is_empty()
    }
}

struct Node {
    id: usize,
    coreness: usize,
    est: Estimates, // est[k] è l'estimate locale della coreness del vicino che ha id k,
    neighbors: Vec<Arc<Mutex<MessageMail>>>, // lista di Message_Mail dei vicini,
    messages: Arc<Mutex<MessageMail>>, // queue di messaggi
    changed: bool,  // indica se è stato cambiato dall'ultima fase di invio messaggi
}

impl Node {
    pub fn new(n: usize) -> Self {
        Node {
            id: n,
            coreness: MAX,
            est: Estimates::new(),
            neighbors: Vec::new(),
            messages: Arc::new(Mutex::new(MessageMail::new(n))),
            changed: true,
        }
    }

    pub fn add_neighbor(&mut self, node: Arc<Mutex<MessageMail>>) {
        // aggiunge un nuovo vicino
        self.neighbors.push(node);
    }

    pub fn init(&mut self) {
        // elimina duplicati, se presenti, dalla lista di vicini
        let mut seen: HashSet<usize> = HashSet::new();

        // usa un HashSet per vedere se gli elementi sono già stati "visti"
        self.neighbors.retain(|x| {
            let id = x.lock().unwrap().id;
            seen.insert(id) // il metodo restituisce true se l'id non è stato ancora inserito
        });

        // inizializza gli estimates dei vicini a "infinito"
        self.est.est.clear();
        for neighbor in &self.neighbors {
            self.est.push((neighbor.lock().unwrap().id, MAX));
        }
        self.est.init();
        // inizializza la propria coreness con la lunghezza della lista di adiacenza
        self.coreness = self.neighbors.len();

        // invia un messaggio a tutti i vicini
        self.changed = true;
        self.send_messages();
    }

    pub fn compute_index(&mut self) -> usize {
        let mut messages = self.messages.lock().unwrap();
        // se la lista di messaggi è vuota non devo calcolare coreness
        if messages.is_empty() {
            return self.coreness;
        }
        // controllo la lista di messaggi e aggiorno gli estimates locali
        while !messages.is_empty() {
            let message = messages.pop().unwrap();
            self.est.insert(message.0, message.1);
        }
        drop(messages);
        let core = self.coreness;

        if core == 0 {
            return 0;
        }

        let mut count: Vec<usize> = Vec::with_capacity(core + 1);
        count.resize(core + 1, 0);

        for neighbor in &self.est.est {
            let k = cmp::min(core, neighbor.1);
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
            self.changed = true;
        }
        self.coreness = i;

        return i;
    }

    pub fn send_messages(&mut self) {
        if self.changed {
            self.changed = false;
            for neighbor in &mut self.neighbors {
                neighbor
                    .lock()
                    .unwrap()
                    .messages
                    .push_back((self.id, self.coreness));
            }
        }
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
        let message_j = Arc::clone(&self.inmap[j].messages);
        let message_i = Arc::clone(&self.inmap[i].messages);

        self.inmap[i].add_neighbor(Arc::clone(&message_j));
        self.inmap[j].add_neighbor(Arc::clone(&message_i));
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
            writeln!(file, "{}", n.coreness)?;
        }

        Ok(())
    }

    // calcolo coreness utilizzando threadpool, dato che creando un nuovo "task" per ogni singolo nodo
    // da elaborare introduce troppo overhead, si usano gli iteratori su chunk
    pub fn compute_coreness_threadpool(
        &mut self,
        num_threads: &usize,
        batch_size: &usize,
    ) -> usize {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(*num_threads)
            .build()
            .unwrap();
        let cont_mutex = RwLock::new(true);
        let mut cont = true;

        let chunk_size = batch_size;

        let mut iter: usize = 0;

        while cont {
            iter += 1;
            let mut guard = cont_mutex.write().unwrap();
            *guard = false;
            drop(guard);
            pool.scope(|scope| {
                for chunk in self.inmap.chunks_mut(*chunk_size) {
                    scope.spawn(|_| {
                        let mut changed = false;
                        for node in chunk.iter_mut() {
                            node.compute_index();
                            changed |= node.changed;
                            node.send_messages();
                        }

                        if changed {
                            let mut guard = cont_mutex.write().unwrap();
                            *guard = true;
                            drop(guard);
                        }
                    });
                }
            });

            let guard = cont_mutex.read().unwrap();
            cont = *guard;
            drop(guard);
        }
        return iter;
    }

    pub fn compute_coreness_iterator(&mut self, num_threads: &usize, _batch_size: &usize) -> usize {
        let mut cont = true;

        let mut rounds = 0;
        rayon::ThreadPoolBuilder::new()
            .num_threads(*num_threads)
            .build()
            .unwrap()
            .install(|| {
                while cont {
                    rounds += 1;

                    // computazione in parallelo dei coreness dei nodi
                    cont = self
                        .inmap
                        .par_iter_mut() // itera in modo parallelo il vettore
                        .map(|x| {
                            let changed = thread_routine_index(x);
                            thread_routine_message(x);
                            return changed;
                        }) // applica la funzione thread_routine_index a ogni elemento
                        .reduce(|| false, |a, b| a || b); // or tra tutti i risultati: se almeno uno è stato cambiato si continua
                }
            });
        return rounds;
    }

    pub fn compute_coreness_threads(&mut self, num_threads: &usize, chunk_size: &usize) -> usize {
        let mut iter: usize = 0;
        thread::scope(|scope| {
            let cont_mutex: Arc<Mutex<bool>> = Arc::new(Mutex::new(true));
            let barrier = Arc::new(Barrier::new(*num_threads + 1));
            let mut threads = Vec::with_capacity(*num_threads);

            let index: Arc<Mutex<usize>> = Arc::new(Mutex::new(0));

            let mut nodes: Vec<Mutex<&mut [Node]>> = Vec::new();

            for chunk in self.inmap.chunks_mut(*chunk_size) {
                nodes.push(Mutex::new(chunk));
            }

            let node_list = Arc::new(nodes);

            for _i in 0..*num_threads {
                let cont_clone = Arc::clone(&cont_mutex);
                let barrier_clone = Arc::clone(&barrier);
                let index_clone = Arc::clone(&index);
                let node_list_clone = Arc::clone(&node_list);

                threads.push(scope.spawn(move || {
                    thread_routine(cont_clone, barrier_clone, index_clone, node_list_clone);
                }));
            }

            let mut continua = true;

            while continua {
                iter += 1;
                let mut cont_guard = cont_mutex.lock().unwrap();
                *cont_guard = false;
                drop(cont_guard);
                barrier.wait();
                // calcolo coreness + invio messaggi

                barrier.wait();
                let mut index_guard = index.lock().unwrap();
                *index_guard = 0;
                drop(index_guard);

                let cont_guard = cont_mutex.lock().unwrap();
                continua = *cont_guard;
                drop(cont_guard);
                barrier.wait();
            }
        });
        return iter;
    }
}

fn thread_routine(
    cont: Arc<Mutex<bool>>,
    barrier: Arc<Barrier>,
    index: Arc<Mutex<usize>>,
    node_list: Arc<Vec<Mutex<&mut [Node]>>>,
) {
    let mut continua = true;
    let index_max = node_list.len();
    while continua {
        barrier.wait();
        continua = false;

        // unica fase, calcolo coreness e invio messaggi
        let mut i = get_and_increment(&index);
        while i < index_max {
            for node in node_list[i].lock().unwrap().iter_mut() {
                node.compute_index();
                continua |= node.changed;
                node.send_messages();
            }
            i = get_and_increment(&index);
        }

        let mut cont_guard = cont.lock().unwrap();
        *cont_guard |= continua;
        drop(cont_guard);
        barrier.wait();
        let cont_guard = cont.lock().unwrap();
        continua = *cont_guard;
        drop(cont_guard);
        barrier.wait();
    }
}

fn get_and_increment(index: &Arc<Mutex<usize>>) -> usize {
    let mut index_guard = index.lock().unwrap();
    let i = *index_guard;
    *index_guard += 1;
    return i;
}
// funzione eseguita dai thread in fase di computazione coreness su ogni nodo
fn thread_routine_index(node: &mut Node) -> bool {
    node.compute_index();
    return node.changed;
}

// funzione eseguita dai thread in fase di invio messaggi
fn thread_routine_message(node: &mut Node) {
    // prende le lock dei MessageMail dei vicini, non dei nodi stessi, così c'è contention solo per l'accesso
    // alla lista di messaggi, non sono possibili deadlock perché si acquisisce una lock alla volta e si
    // rilascia a fine operazione
    node.send_messages();
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

    // algoritmo di calcolo coreness dei nodi con parallel iterator
    start = Instant::now();
    graph.compute_coreness_iterator(&6, &512);
    println!(
        "Per calcolare coreness con parallel iterator: {:?}",
        start.elapsed()
    );

    graph.init_graph();

    // calcolo coreness tramite threadpool
    start = Instant::now();
    graph.compute_coreness_threadpool(&6, &512);
    println!(
        "Per calcolare coreness con threadpool: {:?}",
        start.elapsed()
    );

    // calcolo coreness tramite threads
    graph.init_graph();
    start = Instant::now();
    graph.compute_coreness_threads(&6, &512);
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

    let nums_threads: [usize; 1] = [6];

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
            graph.init_graph();
            let start = Instant::now();
            let iter = graph.compute_coreness_iterator(&num_threads, &0);

            let data = "onephase_iterator".to_owned()
                + ","
                + graph_name
                + ","
                + format!("{:?}", start.elapsed()).as_str()
                + ","
                + "0"
                + ","
                + num_threads.to_string().as_str()
                + ","
                + iter.to_string().as_str()
                + "\n";
            let _n = file.write_all(data.as_bytes());
        }
    }

    for graph_name in graphs {
        let file_name = "./graphs/".to_owned() + graph_name + "/" + graph_name + ".txt";
        let mut graph = Graph::new();

        let _m = graph.parse_file(&file_name);

        for num_threads in nums_threads {
            for chunk_size in batch_sizes {
                graph.init_graph();
                let start = Instant::now();
                let iter = graph.compute_coreness_threadpool(&num_threads, &chunk_size);

                let data = "onephase_threadpool".to_owned()
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

    for graph_name in graphs {
        let file_name = "./graphs/".to_owned() + graph_name + "/" + graph_name + ".txt";
        let mut graph = Graph::new();

        let _m = graph.parse_file(&file_name);

        for num_threads in nums_threads {
            for chunk_size in batch_sizes {
                graph.init_graph();
                let start = Instant::now();
                let iter = graph.compute_coreness_threads(&num_threads, &chunk_size);

                let data = "onephase_threads".to_owned()
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
