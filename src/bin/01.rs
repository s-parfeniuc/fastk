use std::cell::RefCell;
use std::cmp;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::rc::Rc;
use std::time::Instant;
use std::usize::MAX;

/*
Questa versione singlethread simula il comportamento di host diversi che comunicano tra di loro tramite scambi di messaggi
in assenza di un canale broadcast. Ogni nodo ha una coda di messaggi della forma <nodo, nuovo_estimate>. Quando l'estimate
di un nodo cambia, esso invierà un messaggio a tutti i propri vicini.
Alla ricezione di un tale messaggio, il ricevitore calcola il nuovo estimate e in caso di aggiornamento
invia a sua volta messaggi a tutti i propri vicini.
*/

/*
Per rappresentare un grafo creato da nodi che abbiano conoscenza limitata sui propri vicini è necessario
astrarre la logica dei nodi e creare uno struct che rappresenti un'unico nodo. Questo struct avrà
localmente un vettore di nodi vicini (riferimenti a essi) e un vettore che rappresenti le stime associate a
ogni vicino (in questo caso un hashmap per permettere l'accesso costante). L'unico modo che i nodi hanno
di interagire e modificarsi tra di loro è tramite l'invio di messaggi, coppie <id, estimate>. Ogni
nodo ha quindi una coda di messaggi inviatigli dai propri vicini.
*/

/*
Rust permette di avere un solo riferimento mutable o più riferimenti unmutable allo stesso oggetto, nel nostro caso sono
invece necessari più riferimenti mutable ai nodi appartenenti al grafo: ogni nodo deve avere un riferimento a tutti i propri
vicini, e questo riferimento deve essere mutable per permettere l'invio di messaggi (facendo push sulla lista di messaggi).
Per ottenere ciò si possono utilizzare RefCell, che permettono di svincolare un oggetto dai controlli del borrow-checker
statico del compilatore, facendoli invece in runtime; e Rc, reference counter, che permette di clonare un riferimento a un
oggetto contando il numero di riferimenti presenti in runtime.
*/

struct Node {
    id: usize,
    coreness: usize,
    est: HashMap<usize, usize>, // est[k] è l'estimate locale della coreness del vicino che ha id k,
    neighbors: Vec<Rc<RefCell<Node>>>, // lista di vicini, usando referencecounter
    messages: VecDeque<(usize, usize)>, // queue di messaggi
}

impl Node {
    pub fn new(n: usize) -> Self {
        Node {
            id: n,
            coreness: MAX,
            est: HashMap::new(),
            neighbors: Vec::new(),
            messages: VecDeque::new(),
        }
    }

    pub fn add_neighbor(&mut self, node: Rc<RefCell<Node>>) {
        // aggiunge un nuovo vicino
        self.neighbors.push(node);
    }

    pub fn init(&mut self) {
        // elimina duplicati, se presenti, dalla lista di vicini
        let mut seen: HashSet<usize> = HashSet::new();

        // usa un HashSet per vedere se gli elementi sono già stati "visti"
        self.neighbors.retain(|x| {
            let id = x.borrow().id;
            seen.insert(id) // il metodo restituisce true se l'id non è stato ancora inserito
        });

        // inizializza gli estimates dei vicini a "infinito"
        for neighbor in &self.neighbors {
            self.est.insert(neighbor.borrow().id, MAX);
        }

        // inizializza la proprio coreness con la lunghezza della lista di adiacenza
        self.coreness = self.neighbors.len();

        // invia un messaggio a tutti i vicini
        self.send_messages();
    }

    pub fn compute_index(&mut self) -> usize {
        // controllo la lista di messaggi e aggiorno gli estimates locali
        if self.messages.is_empty() {
            return self.coreness;
        }
        while !self.messages.is_empty() {
            let message = self.messages.pop_back().unwrap();
            if message.1 < *self.est.get(&message.0).unwrap() {
                self.est.insert(message.0, message.1);
            }
        }

        let core = self.coreness;

        if core == 0 {
            return 0;
        }

        let mut count: Vec<usize> = Vec::with_capacity(core + 1);
        count.resize(core + 1, 0);

        for neighbor in &self.est {
            let k = cmp::min(core, *neighbor.1);
            count[k] += 1;
        }

        for i in (1..core + 1).rev() {
            count[i - 1] += count[i];
        }

        let mut i = core;
        while i > 1 && count[i] < i {
            i -= 1;
        }

        self.coreness = i;
        if i < core {
            self.send_messages();
        }

        return i;
    }

    fn send_messages(&mut self) {
        for neighbor in &mut self.neighbors {
            neighbor
                .borrow_mut()
                .messages
                .push_back((self.id, self.coreness));
        }
    }
}

struct Graph {
    inmap: Vec<Rc<RefCell<Node>>>,
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
                self.inmap.push(Rc::new(RefCell::new(Node::new(n))));
            }
        }
        if i == j {
            return;
        }
        self.inmap[i]
            .borrow_mut()
            .add_neighbor(Rc::clone(&self.inmap[j]));
        self.inmap[j]
            .borrow_mut()
            .add_neighbor(Rc::clone(&self.inmap[i]));
    }

    // inizializza tutti i nodi con i valori opportuno, chiamata dopo aver aggiunto tutti i nodi
    pub fn init_graph(&mut self) {
        for node in &self.inmap {
            node.borrow_mut().init();
        }
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

    pub fn write_to_file(&self, filename: &str) -> std::io::Result<()> {
        let mut file = File::create(filename)?;

        for n in &self.inmap {
            writeln!(file, "{}", n.borrow().neighbors.len())?;
        }

        Ok(())
    }

    pub fn compute_coreness(&mut self) -> usize {
        let mut cont = true;
        let mut iter = 0;
        while cont {
            cont = false;
            iter += 1;
            for node in &self.inmap {
                let old_coreness = node.borrow().coreness;
                if old_coreness != node.borrow_mut().compute_index() {
                    cont = true;
                }
            }
        }
        iter
    }

    // stampa informazioni sul grafo come numero di nodi e archi
    pub fn print_info(&self) {
        println!("Numero di nodi: {}", self.inmap.len());
        let mut edges = 0;
        for node in &self.inmap {
            edges += node.borrow().neighbors.len();
        }
        println!("Numero di archi: {}", edges / 2);
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
    graph.print_info();
    // algoritmo di calcolo coreness dei nodi
    start = Instant::now();
    graph.compute_coreness();
    println!(
        "Per calcolare coreness single-thread: {:?}",
        start.elapsed()
    );

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

    // apro file in append mode
    let mut file = OpenOptions::new()
        .write(true)
        .append(true)
        .open(data_file)
        .unwrap();
    for _ in 0..5 {
        for graph_name in graphs {
            let file_name = "./graphs/".to_owned() + graph_name + "/" + graph_name + ".txt";
            let mut graph = Graph::new();

            let _m = graph.parse_file(&file_name);

            graph.init_graph();
            let start = Instant::now();
            let iter = graph.compute_coreness();

            let data = "single_threaded".to_owned()
                + ","
                + graph_name
                + ","
                + format!("{:?}", start.elapsed()).as_str()
                + ","
                + "0"
                + ","
                + 1.to_string().as_str()
                + ","
                + iter.to_string().as_str()
                + "\n";
            let _n = file.write_all(data.as_bytes());
        }
    }
}
