#![allow(dead_code)]
#![warn(unused_variables)]
use core::num;
use rand::rngs::SmallRng;
use rand::{Rng, RngCore, SeedableRng};
use rayon::{range_inclusive, vec};
use std::cmp;
use std::cmp::max;
use std::collections::VecDeque;
use std::fs::File;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::{self, BufRead, Write};
use std::time::Instant;

#[inline]
fn ilog2_usize(x: usize) -> usize {
    debug_assert!(x > 0);
    (usize::BITS as usize - 1) - x.leading_zeros() as usize
}
// ===================== MAPPER =====================
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
struct PriorityQueue {
    queues: Vec<VecDeque<usize>>, // bucket per priorità
    first_non_empty: usize,
    len: usize, // elementi totali (facoltativo)
}

impl PriorityQueue {
    pub fn new(max_k: usize) -> Self {
        Self {
            queues: vec![VecDeque::new(); max_k + 1],
            first_non_empty: usize::MAX,
            len: 0,
        }
    }

    pub fn push(&mut self, k: usize, value: usize) {
        if k >= self.queues.len() {
            self.queues.resize(k + 1, VecDeque::new());
        }
        self.queues[k].push_back(value);
        self.first_non_empty = self.first_non_empty.min(k);
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<usize> {
        // trova prima il primo bucket non vuoto
        if self.len == 0 {
            return None;
        }
        while self.first_non_empty < self.queues.len()
            && self.queues[self.first_non_empty].is_empty()
        {
            self.first_non_empty += 1;
        }
        if self.first_non_empty >= self.queues.len() {
            return None;
        }

        let k = self.first_non_empty;
        let node = self.queues[k].pop_front()?;
        self.len -= 1;
        // non aggiorno k qui: verrà avanzato al prossimo pop se ora è vuoto
        Some(node)
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}
struct ApproxPriorityQueue {
    queues: Vec<VecDeque<usize>>, // bucket per priorità
    first_non_empty: usize,
    len: usize, // elementi totali (facoltativo)
    mapper: ExpoSubBuckets,
}

impl ApproxPriorityQueue {
    pub fn new(max_k: usize) -> Self {
        let mapper = ExpoSubBuckets::new(max_k, 512, 64);
        let buckets = mapper.total_buckets();
        Self {
            queues: vec![VecDeque::new(); buckets + 1],
            first_non_empty: usize::MAX,
            len: 0,
            mapper,
        }
    }

    pub fn push(&mut self, prio: usize, value: usize) {
        let k = self.mapper.map(prio);
        if k >= self.queues.len() {
            self.queues.resize(k + 1, VecDeque::new());
        }
        self.queues[k].push_back(value);
        self.first_non_empty = self.first_non_empty.min(k);
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<usize> {
        // trova prima il primo bucket non vuoto
        if self.len == 0 {
            return None;
        }
        while self.first_non_empty < self.queues.len()
            && self.queues[self.first_non_empty].is_empty()
        {
            self.first_non_empty += 1;
        }
        if self.first_non_empty >= self.queues.len() {
            return None;
        }

        let k = self.first_non_empty;
        let node = self.queues[k].pop_front()?;
        self.len -= 1;
        // non aggiorno k qui: verrà avanzato al prossimo pop se ora è vuoto
        Some(node)
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}
struct Graph {
    inmap: Vec<Vec<usize>>,
    max_degree: usize,
}

impl Graph {
    pub fn new() -> Self {
        Graph {
            inmap: Vec::new(),
            max_degree: 0,
        }
    }
    /// Restituisce il grado soglia che separa il top percento dei nodi per grado.
    pub fn top_percent_threshold(&self, percent: f64) -> Option<usize> {
        let n = self.inmap.len();
        if n == 0 {
            return None;
        }

        // Calcola i gradi
        let deg: Vec<usize> = self.inmap.iter().map(|nbrs| nbrs.len()).collect();

        // Numero minimo di nodi da includere (almeno 1)
        let mut k = ((n as f64) * percent).ceil() as usize;
        if k == 0 {
            k = 1;
        }
        if k > n {
            k = n;
        }

        // Copia degli indici dei nodi
        let mut idx: Vec<usize> = (0..n).collect();

        // Quickselect per trovare il k-esimo massimo
        let nth = n - k;
        let (_left, nth_elem, _right) =
            idx.select_nth_unstable_by(nth, |&a, &b| deg[a].cmp(&deg[b]));

        Some(deg[*nth_elem])
    }

    pub fn read_file(&mut self, file_path: &str) -> Result<(), std::io::Error> {
        let file = File::open(file_path)?;
        let reader = io::BufReader::new(file);

        for line in reader.lines() {
            let line = line?;
            if line.starts_with('#') || line.starts_with('%') {
                continue;
            }
            // Parsing anche di righe con numeri separati da ","
            let numbers: Vec<usize> = line
                .split(|c| c == ',' || c == ' ' || c == '\t')
                .filter_map(|s| s.parse().ok())
                .collect();

            if numbers.len() == 2 {
                if numbers[0] < numbers[1] {
                    self.add_edge(numbers[0], numbers[1]);
                    self.add_edge(numbers[1], numbers[0]);
                }
            } else {
                println!("Skipping invalid line: {}", line);
            }
        }
        self.init();
        Ok(())
    }

    pub fn transform_to_dot_file(&self, file_path: &str) {
        let mut file = File::create(file_path).expect("Unable to create file");
        write!(file, "graph G {{ ").expect("unable to write to file");
        for i in 0..self.inmap.len() {
            for &j in &self.inmap[i] {
                if i < j {
                    writeln!(file, "{} -- {};", i, j).expect("Unable to write to file");
                }
            }
        }
        write!(file, "}}").expect("unable to write to file");
    }

    pub fn power_law(num_vertices: usize, edge_budget: usize) -> Self {
        let mut g = Graph::new();
        g.inmap.resize(num_vertices, Vec::new());

        if num_vertices < 2 || edge_budget == 0 {
            return g;
        }

        let max_edges = num_vertices * (num_vertices - 1) / 2;
        let budget = edge_budget.min(max_edges);

        let mut rng = SmallRng::from_os_rng();
        let mut edges_added = 0;

        /* fase 1: piccolo seed iniziale connesso */
        g.add_edge(0, 1);
        edges_added += 2;

        /* vettore dei gradi, usato per il campionamento */
        let mut degrees = vec![0usize; num_vertices];
        degrees[0] = 1;
        degrees[1] = 1;

        /* fase 2: attaccamento preferenziale */
        for v in 2..num_vertices {
            if edges_added >= budget {
                break;
            }

            /* somma dei gradi correnti */
            let total_degree: usize = degrees[..v].iter().sum();
            if total_degree == 0 {
                continue;
            }

            /* selezione di un nodo proporzionale al grado */
            let mut r = rng.random_range(0..total_degree);
            let mut u = 0;

            for i in 0..v {
                if r < degrees[i] {
                    u = i;
                    break;
                }
                r -= degrees[i];
            }

            if !g.inmap[v].contains(&u) {
                g.add_edge(v, u);
                degrees[v] += 1;
                degrees[u] += 1;
                edges_added += 2;
            }
        }

        /* fase 3: aggiunta di archi extra mantenendo il bias */
        while edges_added < budget {
            let total_degree: usize = degrees.iter().sum();
            if total_degree == 0 {
                break;
            }

            let pick = |rng: &mut SmallRng| -> usize {
                let mut r = rng.random_range(0..total_degree);
                for i in 0..num_vertices {
                    if r < degrees[i] {
                        return i;
                    }
                    r -= degrees[i];
                }
                num_vertices - 1
            };

            let u = pick(&mut rng);
            let v = pick(&mut rng);

            if u == v {
                continue;
            }

            if g.inmap[u].contains(&v) {
                continue;
            }

            g.add_edge(u, v);
            degrees[u] += 1;
            degrees[v] += 1;
            edges_added += 2;
        }

        g.max_degree = g.inmap.iter().map(|v| v.len()).max().unwrap_or(0);
        g
    }

    pub fn add_random_semi_cliques(
        &mut self,
        num_semicliques: usize,
        clique_size_range: (usize, usize),
        p_internal: f64,
    ) {
        let num_vertices = self.inmap.len();

        let mut rng = SmallRng::from_os_rng();
        /* fase 2: costruzione delle semi-cricche */
        for _ in 0..num_semicliques {
            let size = rng.random_range(clique_size_range.0..=clique_size_range.1);
            let size = size.min(num_vertices);

            let mut nodes = Vec::with_capacity(size);
            while nodes.len() < size {
                let v = rng.random_range(0..num_vertices);
                if !nodes.contains(&v) {
                    nodes.push(v);
                }
            }

            for i in 0..nodes.len() {
                for j in (i + 1)..nodes.len() {
                    if rng.random::<f64>() < p_internal {
                        let u = nodes[i];
                        let v = nodes[j];

                        if !self.inmap[u].contains(&v) {
                            self.add_edge(u, v);
                        }
                    }
                }
            }
        }
    }

    pub fn add_edge(&mut self, i: usize, j: usize) {
        let max = max(i, j) + 1;
        if self.inmap.len() < max {
            self.inmap.resize(max, Vec::new());
        }

        self.inmap[i].push(j);
        self.inmap[j].push(i);
    }

    pub fn random(num_vertices: usize, num_edges: &mut usize, ensure_connected: bool) -> Self {
        let mut g = Graph::new();

        // inizializza i vettori di adiacenza
        g.inmap.resize(num_vertices, Vec::new());

        if *num_edges > num_vertices * (num_vertices - 1) / 2 {
            *num_edges = num_vertices * (num_vertices - 1) / 2;
        }

        let mut rng = SmallRng::from_os_rng();
        let mut edges_added = 0;

        // fase 1: garantire la connettività (catena lineare)
        if ensure_connected && num_vertices > 1 {
            for i in 0..(num_vertices - 1) {
                g.add_edge(i, i + 1);
                edges_added += 1;
            }
        }

        // fase 2: aggiunta di archi casuali
        while edges_added < *num_edges {
            let range = rng.random_range(0..num_vertices);
            let i = rng.random_range(0..range + 1);
            let j = rng.random_range(0..num_vertices);

            if i == j {
                continue;
            }

            // evita archi duplicati
            if g.inmap[i].contains(&j) || g.inmap[j].contains(&i) {
                continue;
            }

            g.add_edge(i, j);
            edges_added += 2;
        }

        g.max_degree = g.inmap.iter().map(|v| v.len()).max().unwrap_or(0);

        g
    }

    pub fn quasi_regular(num_vertices: usize, target_degree: usize) -> Self {
        let mut g = Graph::new();
        g.inmap.resize(num_vertices, Vec::new());

        let mut rng = SmallRng::from_os_rng();

        let max_edges = num_vertices * (num_vertices - 1) / 2;
        let desired_edges = num_vertices * target_degree / 2;
        let desired_edges = desired_edges.min(max_edges);

        let mut edges_added = 0;

        while edges_added < desired_edges {
            let i = rng.random_range(0..num_vertices);
            let j = rng.random_range(0..num_vertices);

            if i == j {
                continue;
            }

            if g.inmap[i].len() >= target_degree || g.inmap[j].len() >= target_degree {
                continue;
            }

            if g.inmap[i].contains(&j) {
                continue;
            }

            g.add_edge(i, j);
            edges_added += 1;
        }

        g.max_degree = g.inmap.iter().map(|v| v.len()).max().unwrap_or(0);
        g
    }

    pub fn dense_core_with_tails(core_size: usize, tail_length: usize, num_tails: usize) -> Self {
        let num_vertices = core_size + num_tails * tail_length;
        let mut g = Graph::new();
        g.inmap.resize(num_vertices, Vec::new());

        // core denso
        for i in 0..core_size {
            for j in (i + 1)..core_size {
                g.add_edge(i, j);
            }
        }

        // code
        let mut current = core_size;
        let mut rng = SmallRng::from_os_rng();
        for _ in 0..num_tails {
            let attach = rng.random_range(0..core_size);
            g.add_edge(attach, current);

            for i in 0..(tail_length - 1) {
                g.add_edge(current + i, current + i + 1);
            }

            current += tail_length;
        }

        g.max_degree = g.inmap.iter().map(|v| v.len()).max().unwrap_or(0);
        g
    }

    pub fn semi_clique_graph(
        num_vertices: usize,
        edge_budget: usize,
        num_semicliques: usize,
        p_internal: f64,
        clique_size_range: (usize, usize),
        num_hubs: usize,
        p_hub: f64,
    ) -> Self {
        let mut g = Graph::new();
        g.inmap.resize(num_vertices, Vec::new());

        let max_edges = num_vertices * (num_vertices - 1) / 2;
        let budget = edge_budget.min(max_edges);

        let mut rng = SmallRng::from_os_rng();
        let mut edges_added = 0;

        /* fase 0: costruzione del grafo connesso */
        for i in 0..(num_vertices - 1) {
            g.add_edge(i, i + 1);
            edges_added += 2;
        }

        /* fase 1: selezione degli hub */
        let mut hubs = Vec::new();
        let mut hubs_selected = 0;
        while hubs_selected < num_hubs.min(num_vertices) {
            let h = rng.random_range(0..num_vertices);
            if !hubs.contains(&h) {
                hubs.push(h);
                hubs_selected += 1;
            }
        }

        /* fase 2: costruzione delle semi-cricche */
        for _ in 0..num_semicliques {
            if edges_added >= budget {
                break;
            }

            let size = rng.random_range(clique_size_range.0..=clique_size_range.1);
            let size = size.min(num_vertices);

            let mut nodes = Vec::with_capacity(size);
            while nodes.len() < size {
                let v = rng.random_range(0..num_vertices);
                if !nodes.contains(&v) {
                    nodes.push(v);
                }
            }

            for i in 0..nodes.len() {
                for j in (i + 1)..nodes.len() {
                    if edges_added >= budget {
                        break;
                    }

                    if rng.random::<f64>() < p_internal {
                        let u = nodes[i];
                        let v = nodes[j];

                        if !g.inmap[u].contains(&v) {
                            g.add_edge(u, v);
                            edges_added += 2;
                        }
                    }
                }
            }
        }

        /* fase 3: connessioni degli hub */
        for &h in &hubs {
            for v in 0..num_vertices {
                if edges_added >= budget {
                    break;
                }

                if h == v {
                    continue;
                }

                if rng.gen::<f64>() < p_hub {
                    if !g.inmap[h].contains(&v) {
                        g.add_edge(h, v);
                        edges_added += 2;
                    }
                }
            }
        }

        g.max_degree = g.inmap.iter().map(|v| v.len()).max().unwrap_or(0);
        g
    }

    /// Rimuove i duplicati da `inmap` e setta `max_degree` al grado massimo
    pub fn init(&mut self) {
        for i in 0..self.inmap.len() {
            if self.inmap[i].len() > self.max_degree {
                self.max_degree = self.inmap[i].len();
            }
            // Rimuove i duplicati e ordina gli elementi
            self.inmap[i].sort();
            let mut n: usize = 0;
            for j in 1..self.inmap[i].len() {
                if self.inmap[i][n] != self.inmap[i][j] {
                    n += 1;
                    self.inmap[i][n] = self.inmap[i][j];
                }
            }
            self.inmap[i].truncate(n + 1);
        }
    }

    /// calcola la coreness di ogni nodo

    pub fn compute_coreness_fifo_opti2(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        let mut queue = VecDeque::new();
        for i in 0..self.inmap.len() {
            queue.push_back(i);
        }
        let mut i;
        for i in 0..self.inmap.len() {
            queue.push_back(i);
            est[i] = self.inmap[i].len();
        }
        let start = Instant::now();
        while let Some(node) = queue.pop_front() {
            changed[node] = false;
            elaborazioni += 1;
            archi_analizzati += self.inmap[node].len();
            let old_estimate = est[node];
            let degree = self.inmap[node].len();
            let k = cmp::min(old_estimate, degree);

            if k >= count.len() {
                count.resize(k + 1, 0);
            }
            // azzero i primi k elementi di count
            for i in 0..=k {
                count[i] = 0;
            }

            // istogramma dei gradi dei vicini
            for neighbor in &self.inmap[node] {
                let k = cmp::min(old_estimate, est[*neighbor]);
                count[k] += 1;
            }

            i = k;
            while i > 1 {
                count[i - 1] += count[i];
                if count[i] >= i {
                    break;
                }
                i -= 1;
            }

            let new_estimate = i;
            if new_estimate != old_estimate {
                changes += 1;
            }

            if new_estimate < old_estimate {
                for &neighbor in &self.inmap[node] {
                    if !changed[neighbor]
                        && new_estimate < est[neighbor]
                        && old_estimate >= est[neighbor]
                    {
                        queue.push_back(neighbor);
                        changed[neighbor] = true;
                    }
                }
                est[node] = new_estimate;
            }
        }
        println!(
            "Ottimizzazione 2: Elaborazioni: {} / {}, Cambiamenti: {} / {}, Archi analizzati: {} / {}, in {:?}",
            elaborazioni,
            self.inmap.len(),
            changes,
            elaborazioni,
            archi_analizzati,
            self.inmap.iter().map(|v| v.len()).sum::<usize>(),
            start.elapsed()
        );
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );
        est
    }

    pub fn compute_coreness_fifo(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        let mut queue = VecDeque::new();
        for i in 0..self.inmap.len() {
            queue.push_back(i);
        }
        let mut i;
        for i in 0..self.inmap.len() {
            queue.push_back(i);
            est[i] = self.inmap[i].len();
        }
        let start = Instant::now();
        while let Some(node) = queue.pop_front() {
            changed[node] = false;
            elaborazioni += 1;
            archi_analizzati += self.inmap[node].len();
            let old_estimate = est[node];
            let degree = self.inmap[node].len();
            let k = cmp::min(old_estimate, degree);

            if k >= count.len() {
                count.resize(k + 1, 0);
            }
            // azzero i primi k elementi di count
            for i in 0..=k {
                count[i] = 0;
            }

            // istogramma dei gradi dei vicini
            for neighbor in &self.inmap[node] {
                let k = cmp::min(old_estimate, est[*neighbor]);
                count[k] += 1;
            }

            i = k;
            while i > 1 {
                count[i - 1] += count[i];
                if count[i] >= i {
                    break;
                }
                i -= 1;
            }

            let new_estimate = i;
            if new_estimate != old_estimate {
                changes += 1;
            }

            if new_estimate < old_estimate {
                for &neighbor in &self.inmap[node] {
                    if !changed[neighbor] {
                        queue.push_back(neighbor);
                        changed[neighbor] = true;
                    }
                }
                est[node] = new_estimate;
            }
        }
        println!(
            "Senza ottimizzazioni: Elaborazioni: {} / {}, Cambiamenti: {} / {}, Archi analizzati: {} / {}, in {:?}",
            elaborazioni,
            self.inmap.len(),
            changes,
            elaborazioni,
            archi_analizzati,
            self.inmap.iter().map(|v| v.len()).sum::<usize>(),
            start.elapsed()
        );
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );
        est
    }

    pub fn compute_coreness_fifo_opti1(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        let mut queue = VecDeque::new();
        for i in 0..self.inmap.len() {
            queue.push_back(i);
        }
        let mut i;
        for i in 0..self.inmap.len() {
            queue.push_back(i);
            est[i] = self.inmap[i].len();
        }
        let start = Instant::now();
        while let Some(node) = queue.pop_front() {
            changed[node] = false;
            elaborazioni += 1;
            archi_analizzati += self.inmap[node].len();
            let old_estimate = est[node];
            let degree = self.inmap[node].len();
            let k = cmp::min(old_estimate, degree);

            if k >= count.len() {
                count.resize(k + 1, 0);
            }
            // azzero i primi k elementi di count
            for i in 0..=k {
                count[i] = 0;
            }

            // istogramma dei gradi dei vicini
            for neighbor in &self.inmap[node] {
                let k = cmp::min(old_estimate, est[*neighbor]);
                count[k] += 1;
            }

            i = k;
            while i > 1 {
                count[i - 1] += count[i];
                if count[i] >= i {
                    break;
                }
                i -= 1;
            }

            let new_estimate = i;
            if new_estimate != old_estimate {
                changes += 1;
            }

            if new_estimate < old_estimate {
                for &neighbor in &self.inmap[node] {
                    if !changed[neighbor] && new_estimate < est[neighbor] {
                        queue.push_back(neighbor);
                        changed[neighbor] = true;
                    }
                }
                est[node] = new_estimate;
            }
        }
        println!(
            "Ottimizzazione 1: Elaborazioni: {} / {}, Cambiamenti: {} / {}, Archi analizzati: {} / {}, in {:?}",
            elaborazioni,
            self.inmap.len(),
            changes,
            elaborazioni,
            archi_analizzati,
            self.inmap.iter().map(|v| v.len()).sum::<usize>(),
            start.elapsed()
        );
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );
        est
    }

    /*
        pub fn compute_coreness_dynamic_priority(&mut self) -> Vec<usize> {
            let mut est: Vec<usize> = vec![0; self.inmap.len()];
            let mut changed: Vec<bool> = vec![true; self.inmap.len()];
            let mut stability: Vec<isize> = vec![-1; self.inmap.len()];

            let mut elaborazioni = 0;
            let mut changes = 0;

            let mut archi_analizzati = 0;

            let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

            let mut priority_queue = PriorityQueue::new(128);
            let mut i;
            for i in 0..self.inmap.len() {
                est[i] = self.inmap[i].len();
                priority_queue.push(est[i], i);
            }

            let start = Instant::now();
            while let Some(j) = priority_queue.pop() {
                changed[j] = false;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                stability[j] = 0;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        stability[j] = (count[i] - i) as isize;
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;
                est[j] = new_estimate;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        if new_estimate < est[neighbor] && old_estimate >= est[neighbor] {
                            if stability[neighbor] >= 0 {
                                stability[neighbor] = -1;
                            }
                            if changed[neighbor] {
                                if (est[neighbor] - new_estimate) as isize > -stability[neighbor] {
                                    stability[neighbor] -=
                                        est[neighbor] as isize - new_estimate as isize;
                                    priority_queue.increase_priority(neighbor);
                                }
                            }
                            if !changed[neighbor] && stability[neighbor] < 0 {
                                priority_queue.push(est[neighbor], neighbor);
                                changed[neighbor] = true;
                            }
                        }
                    }
                    changes += 1;
                } else {
                    if new_estimate == self.inmap[j].len() {
                        changes += 1;
                    }
                }
            }
            println!("---Dynamic priority---");
            println!("Tempo: {:?}", start.elapsed());
            println!(
                "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
                elaborazioni as f64 / self.inmap.len() as f64,
                changes as f64 / elaborazioni as f64,
                archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
            );
            est
        }
    */

    pub fn compute_coreness_iter_sync_approx(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut stability: Vec<isize> = vec![-1; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;
        let mut iterazioni = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        let start = Instant::now();
        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
        }
        let mut i;
        let mut finish = false;

        let mut local_elaborations: Vec<u8> = vec![0; self.inmap.len()];
        let mut priority_queue: ApproxPriorityQueue = ApproxPriorityQueue::new(self.max_degree);
        for i in 0..self.inmap.len() {
            priority_queue.push(est[i], i);
        }
        println!("Tempo inizializzazione: {:?}", start.elapsed());
        while !finish {
            finish = true;
            iterazioni += 1;
            if iterazioni != 1 {
                for j in 0..self.inmap.len() {
                    local_elaborations[j] = 0;
                    if changed[j] {
                        priority_queue.push(est[j], j);
                    }
                }
            }

            while let Some(j) = priority_queue.pop() {
                changed[j] = false;
                local_elaborations[j] += 1;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                stability[j] = 0;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        stability[j] = (count[i] - i) as isize;
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;
                est[j] = new_estimate;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        if new_estimate < est[neighbor] && old_estimate >= est[neighbor] {
                            stability[neighbor] -= 1;
                            if !changed[neighbor] && stability[neighbor] < 0 {
                                if local_elaborations[neighbor] < 1 {
                                    priority_queue.push(est[neighbor], neighbor);
                                }
                                changed[neighbor] = true;
                            }
                        }
                    }
                    changes += 1;
                    finish = false;
                } else {
                    if iterazioni == 1 && local_elaborations[j] == 1 {
                        changes += 1;
                    }
                }
            }
        }

        println!("---Approx---");
        println!("Tempo: {:?}", start.elapsed());
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );
        println!(
            "Max degree: {}, Buckets: {}",
            self.max_degree,
            priority_queue.mapper.total_buckets()
        );

        est
    }

    pub fn compute_coreness_iter_sync_opti2(
        &mut self,
        factors: (f64, f64),
        archi: &mut f64,
        debug: bool,
    ) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut stability: Vec<isize> = vec![-1; self.inmap.len()];

        const DEBUG: bool = false;

        let mut potential: Vec<u16> = vec![0; self.inmap.len()];
        let mut elaborations: Vec<u16> = vec![0; self.inmap.len()];

        let mut rng = SmallRng::from_os_rng();

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;
        let mut iterazioni = 0;
        let mut skip: Vec<bool> = vec![false; self.inmap.len()];

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        let start = Instant::now();
        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
        }
        let mut i;
        let mut finish = false;

        let threshold = self.top_percent_threshold(0.05).unwrap_or(usize::MAX);
        let is_high_degree = |node: usize| self.inmap[node].len() >= threshold;

        let mut last_updated: Vec<u8> = vec![0; self.inmap.len()];
        let mut priority_queue: PriorityQueue = PriorityQueue::new(128);

        for i in 0..self.inmap.len() {
            priority_queue.push(est[i], i);
        }

        let mut equal_estimates = 0;
        let mut final_step = false;
        while !finish {
            finish = true;
            iterazioni += 1;
            if iterazioni != 1 {
                for j in 0..self.inmap.len() {
                    if stability[j] < 0 {
                        priority_queue.push(est[j], j);
                    }
                    elaborations[j] = 0;
                }
            }
            let est_factor: f64 = factors.0;
            let potential_factor: f64 = factors.1;

            while let Some(j) = priority_queue.pop() {
                skip[j] = false;
                last_updated[j] = iterazioni as u8;

                elaborations[j] += 1;

                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];

                let k = old_estimate;

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }
                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                let old_stability = stability[j];
                stability[j] = 0;
                let old_potential = potential[j];
                potential[j] = count[i] as u16;
                while i > 1 {
                    if count[i] >= i {
                        stability[j] = (count[i] - i) as isize;
                        break;
                    }
                    potential[j] = count[i - 1] as u16;
                    count[i - 1] += count[i];
                    i -= 1;
                }
                if DEBUG {
                    println!(
                        "{} [{}] Inizio: ({}, {}), ({}) -> ({}, {}, {})",
                        iterazioni,
                        j,
                        est[j],
                        old_stability,
                        old_potential,
                        i,
                        stability[j],
                        potential[j]
                    );
                }

                let new_estimate = i;
                est[j] = new_estimate;
                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        if new_estimate < est[neighbor] + cmp::min(stability[neighbor] as usize, 0)
                            && old_estimate >= est[neighbor]
                        {
                            stability[neighbor] -= 1;
                            if stability[neighbor] == -1 && elaborations[neighbor] < 1 {
                                priority_queue.push(
                                    (est[neighbor] as f64 * est_factor
                                        + potential[neighbor] as f64 * potential_factor)
                                        as usize,
                                    neighbor,
                                );
                            }
                        }
                    }
                    changes += 1;
                    finish = false;
                } else {
                    if iterazioni == 1 {
                        changes += 1;
                    }
                }
            }
            if finish && !final_step {
                final_step = true;
                finish = false;
                for j in 0..self.inmap.len() {
                    if last_updated[j] == 0 {
                        priority_queue.push(est[j], j);
                    }
                }
            }
        }
        if debug {
            println!("---Stability--- [{}, {}]", factors.0, factors.1);
            println!("Tempo: {:?}", start.elapsed());
            println!(
                "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}, Stime uguali: {}",
                elaborazioni as f64 / self.inmap.len() as f64,
                changes as f64 / elaborazioni as f64,
                archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64,
                equal_estimates,
            );
        }

        *archi = archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64;
        let mut archi_per_elaborazioni = Vec::new();
        let mut count_elaborazioni = Vec::new();
        for (i, &elab) in elaborations.iter().enumerate() {
            let len = archi_per_elaborazioni.len();
            if elab as usize >= len {
                archi_per_elaborazioni.resize_with(elab as usize + 1, || 0);
                count_elaborazioni.resize_with(elab as usize + 1, || 0);
            }
            archi_per_elaborazioni[elab as usize] += self.inmap[i].len() * elab as usize;
            count_elaborazioni[elab as usize] += 1;
        }
        /*
        let mut sum: f64 = 0.0;
        for level in 0..archi_per_elaborazioni.len() {
            let archi = archi_per_elaborazioni[level];
            let count = count_elaborazioni[level];
            println!(
                "Livello {}: Archi = {}, Conteggio = {}",
                level,
                archi as f64 / archi_analizzati as f64,
                count
            );
            sum += archi as f64 / archi_analizzati as f64;
        }
        println!("Somma totale: {} (dovrebbe essere 1)", sum);
        */
        est
    }

    pub fn compute_coreness_iter_sync_opti2_simplified(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut stability: Vec<isize> = vec![-1; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;
        let mut iterazioni = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        let start = Instant::now();
        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
        }
        let mut i;
        let mut finish = false;

        let mut local_elaborations: Vec<u8> = vec![0; self.inmap.len()];
        let mut priority_queue: PriorityQueue = PriorityQueue::new(128);
        for i in 0..self.inmap.len() {
            priority_queue.push(est[i], i);
        }
        println!("Tempo inizializzazione: {:?}", start.elapsed());
        while !finish {
            finish = true;
            iterazioni += 1;
            if iterazioni != 1 {
                for j in 0..self.inmap.len() {
                    local_elaborations[j] = 0;
                    if changed[j] {
                        priority_queue.push(est[j], j);
                    }
                }
            }

            while let Some(j) = priority_queue.pop() {
                changed[j] = false;
                local_elaborations[j] += 1;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                stability[j] = 0;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        stability[j] = (count[i] - i) as isize;
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;
                est[j] = new_estimate;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        if new_estimate < est[neighbor] && old_estimate >= est[neighbor] {
                            stability[neighbor] -= 1;
                            if !changed[neighbor] && stability[neighbor] < 0 {
                                if local_elaborations[neighbor] < 1 {}
                                changed[neighbor] = true;
                            }
                        }
                    }
                    changes += 1;
                    finish = false;
                } else {
                    if iterazioni == 1 && local_elaborations[j] == 1 {
                        changes += 1;
                    }
                }
            }
        }

        println!("---Stability No Reinsert---");
        println!("Tempo: {:?}", start.elapsed());
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn compute_coreness_iter_sync_opti3(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut stability: Vec<isize> = vec![-1; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut priority_queue: PriorityQueue = PriorityQueue::new(128);

        let elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
            if est[i] < 1 {
                continue;
            }
            if est[i] == 2 {
                priority_queue.push(2, i);
            } else {
                priority_queue.push(3, i);
            }
        }
        let start = Instant::now();
        let mut i;
        //estraggo dalla lista prioritaria finché non è vuota
        while let Some(j) = priority_queue.pop() {
            changed[j] = false;
            archi_analizzati += self.inmap[j].len();
            let old_estimate = est[j];
            let degree = self.inmap[j].len();
            let k = cmp::min(old_estimate, degree);

            if k >= count.len() {
                count.resize(k + 1, 0);
            }
            // azzero i primi k elementi di count
            for i in 0..=k {
                count[i] = 0;
            }

            // istogramma dei gradi dei vicini
            for neighbor in &self.inmap[j] {
                let k = cmp::min(old_estimate, est[*neighbor]);
                count[k] += 1;
            }

            i = k;
            stability[j] = 0;
            while i > 1 {
                count[i - 1] += count[i];
                if count[i] >= i {
                    stability[j] = (count[i] - i) as isize;
                    break;
                }
                i -= 1;
            }

            let new_estimate = i;
            est[j] = new_estimate;

            if new_estimate < old_estimate {
                for &neighbor in &self.inmap[j] {
                    if new_estimate < est[neighbor] && old_estimate >= est[neighbor] {
                        stability[neighbor] -= 1;
                        if !changed[neighbor] && stability[neighbor] < 0 {
                            priority_queue.push(est[neighbor], neighbor);
                            changed[neighbor] = true;
                        }
                    }
                }
                changes += 1;
            } else {
                if new_estimate == self.inmap[j].len() {
                    changes += 1;
                }
            }
        }

        println!("---Priority Queue---");
        println!("Tempo: {:?}", start.elapsed());
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn compute_coreness_iter_sync_opti1(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;
        let mut _iterazioni: usize = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
        }
        let start = Instant::now();
        let mut i;
        let mut finish = false;
        while !finish {
            finish = true;
            _iterazioni += 1;
            for j in 0..self.inmap.len() {
                if !changed[j] {
                    continue;
                }
                changed[j] = false;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;
                est[j] = new_estimate;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        if new_estimate < est[neighbor] && old_estimate >= est[neighbor] {
                            changed[neighbor] = true;
                        }
                    }
                    changes += 1;
                    finish = false;
                }
            }
        }

        println!("---Subrounds--- ");
        println!("Tempo: {:?}", start.elapsed());
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn compute_coreness_iter_sync(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;
        let mut iterazioni = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
        }
        let start = Instant::now();
        let mut i;
        let mut finish = false;
        while !finish {
            finish = true;
            iterazioni += 1;
            for j in 0..self.inmap.len() {
                if !changed[j] {
                    continue;
                }
                changed[j] = false;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;
                est[j] = new_estimate;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        changed[neighbor] = true;
                    }
                    changes += 1;
                    finish = false;
                }
            }
        }

        println!(
            "Senza ottimizzazioni: Elaborazioni: {} / {}, Cambiamenti: {} / {}, Archi analizzati: {} / {}, Iterazioni: {}, in {:?}",
            elaborazioni,
            self.inmap.len(),
            changes,
            elaborazioni,
            archi_analizzati,
            self.inmap.iter().map(|v| v.len()).sum::<usize>(),
            iterazioni,
            start.elapsed()
        );
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn compute_coreness_iter_async_opti2(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut local_changes: Vec<(usize, usize)> = Vec::new(); // (node, old_estimate)
        let mut local_activated_nodes: Vec<(usize, usize)> = Vec::new(); //(neighbor, old_estimate)

        let mut archi_analizzati = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
        }
        let start = Instant::now();
        let mut i;
        let mut finish = false;
        while !finish {
            finish = true;
            for j in 0..self.inmap.len() {
                if !changed[j] {
                    continue;
                }
                changed[j] = false;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        if new_estimate < est[neighbor] {
                            local_activated_nodes.push((neighbor, old_estimate));
                        }
                    }
                    changes += 1;
                    local_changes.push((j, new_estimate));
                    finish = false;
                }
            }

            for (node, new_estimate) in local_changes.drain(..) {
                est[node] = new_estimate;
            }

            for (neighbor, old_estimate) in local_activated_nodes.drain(..) {
                if old_estimate >= est[neighbor] {
                    changed[neighbor] = true;
                }
            }
        }
        println!("---Vecchio---");
        println!("Tempo: {:?}", start.elapsed());
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn compute_coreness_iter_async_opti1(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut local_changes: Vec<(usize, usize)> = Vec::new(); // (node, old_estimate)
        let mut local_activated_nodes: Vec<(usize, usize)> = Vec::new(); //(neighbor, old_estimate)

        let mut archi_analizzati = 0;
        let mut iterazioni = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
        }
        let start = Instant::now();
        let mut i;
        let mut finish = false;
        while !finish {
            finish = true;
            iterazioni += 1;
            for j in 0..self.inmap.len() {
                if !changed[j] {
                    continue;
                }
                changed[j] = false;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        if new_estimate < est[neighbor] {
                            local_activated_nodes.push((neighbor, old_estimate));
                        }
                    }
                    changes += 1;
                    local_changes.push((j, new_estimate));
                    finish = false;
                }
            }

            for (node, new_estimate) in local_changes.drain(..) {
                est[node] = new_estimate;
            }

            for (neighbor, _) in local_activated_nodes.drain(..) {
                changed[neighbor] = true;
            }
        }

        println!(
            "Ottimizzazione 2: Elaborazioni: {} / {}, Cambiamenti: {} / {}, Archi analizzati: {} / {}, Iterazioni: {}, in {:?}",
            elaborazioni,
            self.inmap.len(),
            changes,
            elaborazioni,
            archi_analizzati,
            self.inmap.iter().map(|v| v.len()).sum::<usize>(),
            iterazioni,
            start.elapsed()
        );
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn compute_coreness_iter_async(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut local_changes: Vec<(usize, usize)> = Vec::new(); // (node, old_estimate)
        let mut local_activated_nodes: Vec<(usize, usize)> = Vec::new(); //(neighbor, old_estimate)

        let mut archi_analizzati = 0;
        let mut iterazioni = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
        }
        let start = Instant::now();
        let mut i;
        let mut finish = false;
        while !finish {
            finish = true;
            iterazioni += 1;
            for j in 0..self.inmap.len() {
                if !changed[j] {
                    continue;
                }
                changed[j] = false;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        local_activated_nodes.push((neighbor, old_estimate));
                    }
                    changes += 1;
                    local_changes.push((j, new_estimate));
                    finish = false;
                }
            }

            for (node, new_estimate) in local_changes.drain(..) {
                est[node] = new_estimate;
            }

            for (neighbor, _) in local_activated_nodes.drain(..) {
                changed[neighbor] = true;
            }
        }

        println!(
            "Ottimizzazione 2: Elaborazioni: {} / {}, Cambiamenti: {} / {}, Archi analizzati: {} / {}, Iterazioni: {}, in {:?}",
            elaborazioni,
            self.inmap.len(),
            changes,
            elaborazioni,
            archi_analizzati,
            self.inmap.iter().map(|v| v.len()).sum::<usize>(),
            iterazioni,
            start.elapsed()
        );
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn compute_priority(&mut self, priority: Vec<(usize, usize)>) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];

        let max_priority = priority.iter().map(|&(_, p)| p).max().unwrap_or(0);

        let mut priority_queue = PriorityQueue::new(max_priority + 1);

        for (node, priority) in priority {
            priority_queue.push(priority, node);
            est[node] = self.inmap[node].len();
        }
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        let start = Instant::now();
        let mut i;
        while let Some(node) = priority_queue.pop() {
            changed[node] = false;
            elaborazioni += 1;
            archi_analizzati += self.inmap[node].len();
            let old_estimate = est[node];
            let degree = self.inmap[node].len();
            let k = cmp::min(old_estimate, degree);

            if k >= count.len() {
                count.resize(k + 1, 0);
            }
            // azzero i primi k elementi di count
            for i in 0..=k {
                count[i] = 0;
            }

            // istogramma dei gradi dei vicini
            for neighbor in &self.inmap[node] {
                let k = cmp::min(old_estimate, est[*neighbor]);
                count[k] += 1;
            }

            i = k;
            while i > 1 {
                count[i - 1] += count[i];
                if count[i] >= i {
                    break;
                }
                i -= 1;
            }

            let new_estimate = i;
            if new_estimate != old_estimate {
                changes += 1;
            }

            if new_estimate < old_estimate {
                for &neighbor in &self.inmap[node] {
                    if !changed[neighbor]
                        && new_estimate < est[neighbor]
                        && old_estimate >= est[neighbor]
                    {
                        priority_queue.push(est[neighbor], neighbor);
                        changed[neighbor] = true;
                    }
                }
                est[node] = new_estimate;
            }
        }
        println!(
            "Coda prioritaria: Elaborazioni: {} / {}, Cambiamenti: {} / {}, Archi analizzati: {} / {}, in {:?}",
            elaborazioni,
            self.inmap.len(),
            changes,
            elaborazioni,
            archi_analizzati,
            self.inmap.iter().map(|v| v.len()).sum::<usize>(),
            start.elapsed()
        );
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn compute_priority_batagelj(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut priorities: Vec<usize> = vec![0; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;
        let mut iterazioni = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
            priorities[i] = est[i];
        }
        let start = Instant::now();
        let mut i;
        let mut finish = false;

        while !finish {
            finish = true;
            if iterazioni > 10 {
                // iterazioni viene incrementato di più dopo le prime dieci iterazioni, in base al valore attuale
                iterazioni = iterazioni + ((iterazioni as f32).log2() * 5.0) as usize;
            } else {
                iterazioni += 1;
            }
            println!("Iterazione {}", iterazioni);
            for j in 0..self.inmap.len() {
                if !changed[j] {
                    continue;
                }
                if priorities[j] > iterazioni {
                    finish = false;
                    continue;
                }
                changed[j] = false;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;
                est[j] = new_estimate;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        if !changed[neighbor]
                            && new_estimate < est[neighbor]
                            && old_estimate >= est[neighbor]
                        {
                            changed[neighbor] = true;
                            priorities[neighbor] -= 1;
                        }
                    }
                    changes += 1;
                    finish = false;
                }
            }
        }

        println!(
            "Coda di priorità: Elaborazioni: {} / {}, Cambiamenti: {} / {}, Archi analizzati: {} / {}, Iterazioni: {}, in {:?}",
            elaborazioni,
            self.inmap.len(),
            changes,
            elaborazioni,
            archi_analizzati,
            self.inmap.iter().map(|v| v.len()).sum::<usize>(),
            iterazioni,
            start.elapsed()
        );
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn compute_coreness_random(&mut self) -> Vec<usize> {
        let mut est: Vec<usize> = vec![0; self.inmap.len()];
        let mut stability: Vec<isize> = vec![-1; self.inmap.len()];
        let mut changed: Vec<bool> = vec![true; self.inmap.len()];

        let mut elaborazioni = 0;
        let mut changes = 0;

        let mut archi_analizzati = 0;
        let mut iterazioni = 0;

        let mut count: Vec<usize> = vec![0; 1024]; // dimensione arbitraria, può essere aumentata se necessario

        let start = Instant::now();
        for i in 0..self.inmap.len() {
            est[i] = self.inmap[i].len();
        }
        let mut i;
        let mut finish = false;

        let mut local_elaborations: Vec<u8> = vec![0; self.inmap.len()];
        let mut priority_queue: PriorityQueue = PriorityQueue::new(128);
        let max = self.max_degree;
        let mut rng = SmallRng::try_from_os_rng().unwrap();
        for i in 0..self.inmap.len() {
            priority_queue.push(rng.next_u64() as usize % max, i);
        }
        println!("Tempo inizializzazione: {:?}", start.elapsed());
        while !finish {
            finish = true;
            iterazioni += 1;
            if iterazioni != 1 {
                for j in 0..self.inmap.len() {
                    if stability[j] < 0 {
                        priority_queue.push(rng.next_u64() as usize % max, j);
                        changed[j] = true;
                    }
                }
            }
            while let Some(j) = priority_queue.pop() {
                changed[j] = false;
                local_elaborations[j] = iterazioni as u8;
                elaborazioni += 1;
                archi_analizzati += self.inmap[j].len();
                let old_estimate = est[j];
                let degree = self.inmap[j].len();
                let k = cmp::min(old_estimate, degree);

                if k >= count.len() {
                    count.resize(k + 1, 0);
                }
                // azzero i primi k elementi di count
                for i in 0..=k {
                    count[i] = 0;
                }

                // istogramma dei gradi dei vicini
                for neighbor in &self.inmap[j] {
                    let k = cmp::min(old_estimate, est[*neighbor]);
                    count[k] += 1;
                }

                i = k;
                stability[j] = 0;
                while i > 1 {
                    count[i - 1] += count[i];
                    if count[i] >= i {
                        stability[j] = (count[i] - i) as isize;
                        break;
                    }
                    i -= 1;
                }

                let new_estimate = i;
                est[j] = new_estimate;

                if new_estimate < old_estimate {
                    for &neighbor in &self.inmap[j] {
                        if new_estimate < est[neighbor] && old_estimate >= est[neighbor] {
                            stability[neighbor] -= 1;
                            if !changed[neighbor] && stability[neighbor] < 0 {
                                if local_elaborations[neighbor] < iterazioni as u8 {
                                    priority_queue.push(rng.next_u64() as usize % max, neighbor);
                                }
                                changed[neighbor] = true;
                            }
                        }
                    }
                    changes += 1;
                    finish = false;
                } else {
                    if iterazioni == 1 && local_elaborations[j] == 1 {
                        changes += 1;
                    }
                }
            }
        }

        println!("---Random---");
        println!("Tempo: {:?}", start.elapsed());
        println!(
            "Elaborazioni: {}, Cambiamenti: {}, Archi analizzati: {}",
            elaborazioni as f64 / self.inmap.len() as f64,
            changes as f64 / elaborazioni as f64,
            archi_analizzati as f64 / self.inmap.iter().map(|v| v.len()).sum::<usize>() as f64
        );

        est
    }

    pub fn standardize_graph(&self, path: &str) -> Result<(), std::io::Error> {
        let file = File::create(path)?;
        let mut bufwriter = BufWriter::new(file);
        for (i, neighbors) in self.inmap.iter().enumerate() {
            for neighbor in neighbors {
                bufwriter.write(format!("{} {}\n", i, neighbor).as_bytes())?;
            }
        }
        Ok(())
    }
}

pub fn write_file(coreness: Vec<usize>, file_path: &str) -> Result<(), std::io::Error> {
    let file = File::create(file_path)?;
    let mut bufwriter = BufWriter::new(file);
    for &core in coreness.iter() {
        bufwriter.write(format!("{}\n", core).as_bytes())?;
    }
    Ok(())
}

fn main() -> io::Result<()> {
    // gestione argomenti passati da linea di comando: in_file (file da parsare) e out_file (file su cui scrivere la coreness dei nodi)
    let args: Vec<String> = std::env::args().collect();
    sgama_grafi();
    return Ok(());
    if args.len() < 3 || args.len() > 5 {
        println!("2 argomenti: file di input e file in cui scrivere, -t opzionale per settare il numero di thread");
        return Ok(());
    }

    let in_file = &args[1];
    let out_file = &args[2];

    let mut coreness: Vec<usize> = Vec::new();
    let mut start = Instant::now();
    //let mut graph = Graph::new();
    //graph.read_file(in_file)?;

    let mut edges = 3000;
    let nodes = 150;

    let num_semicliques = 10;
    let p_internal = 0.9;
    let clique_size_range = (20, 30);
    let num_hubs = 2;
    let p_hub = 0.5;

    let mut graph = Graph::semi_clique_graph(
        nodes,
        edges,
        num_semicliques,
        p_internal,
        clique_size_range,
        num_hubs,
        p_hub,
    );
    println!("Grafo caricato in {:?}", start.elapsed());

    graph.transform_to_dot_file("./random.dot");
    graph.standardize_graph("./standardized_random.txt")?;

    // leggo il secondo argomento e metto nel vettore coreness quello che leggo su ogni riga
    let reader = BufReader::new(File::open(out_file)?);

    start = Instant::now();
    for line in reader.lines() {
        let line = line?;
        let value = line.parse::<usize>().unwrap_or(0);
        coreness.push(value);
    }

    println!("Per parsare i file: {:?}", start.elapsed());
    println!(
        "Numero di nodi: {}, Numero di archi: {} / {}",
        graph.inmap.len(),
        graph.inmap.iter().map(|v| v.len()).sum::<usize>(),
        nodes * (nodes - 1) / 2
    );

    let factors = [(1.0, 0.0)];
    let mut archi_analizzati: f64 = 0.0;
    for &factors in &factors {
        let core = graph.compute_coreness_iter_sync_opti2(factors, &mut archi_analizzati, true);

        //coreness massima e media
        let max_coreness = core.iter().max().unwrap();
        let avg_coreness = core.iter().sum::<usize>() as f64 / core.len() as f64;
        let avg_degree = edges as f64 / nodes as f64;
        let max_degree = graph.max_degree;
        println!(
            "Coreness massima: {}, Coreness media: {}, Grado medio: {}, Grado massimo: {}",
            max_coreness, avg_coreness, avg_degree, max_degree
        );
        write_file(core, "./coree.txt")?
    }

    Ok(())
}

fn sgama_grafi() {
    let scale = 5.0;
    let nodes = (50 as f64 * scale) as usize;
    let initial_edges = nodes;
    let mut budget;

    let times = 100;

    let max_edges = (((nodes * (nodes - 1)) / 2) - initial_edges) / times;

    let mut archi = 0.0;
    let mut core = Vec::new();
    let mut best_graph = Graph::new();
    let mut max = 0.0;
    let mut iter: usize = 100;

    let mut cliques = vec![0, 1, 2, 3, 4, 5];
    cliques = cliques
        .iter()
        .map(|x| (*x as f64 * scale) as usize)
        .collect::<Vec<usize>>();

    let mut ranges: Vec<(usize, usize)> = vec![(3, 5), (5, 7), (6, 9), (8, 11), (10, 14)];
    ranges = ranges
        .iter()
        .map(|&(a, b)| ((a as f64 * scale) as usize, (b as f64 * scale) as usize))
        .collect();

    let mut rng = SmallRng::from_os_rng();

    let mut graph;
    for i in 0..=times {
        for _ in 0..iter {
            let cliques_id = rng.random_range(0..cliques.len());
            let clique_size_range = ranges[rng.random_range(0..ranges.len())];

            let num_cliques = cliques[cliques_id];
            let p_internal = 0.8;

            budget = initial_edges + max_edges * i;

            budget -= cliques[cliques_id] * (clique_size_range.1 + (clique_size_range.1)) / 2;
            budget = budget.min((nodes * (nodes - 1)) / 2);
            budget = budget.max(nodes - 1);

            iter += 1;
            graph = Graph::power_law(nodes, budget);

            graph.add_random_semi_cliques(num_cliques, clique_size_range, p_internal);

            core = graph.compute_coreness_iter_sync_opti2((1.0, 0.0), &mut archi, false);
            if archi > max {
                best_graph = graph;
                max = archi;
                println!(
                    "Nuovo massimo di archi analizzati / archi: {} (N:{}, E:{}) (Cricche: {}, Size: {:?})",
                    max, nodes, budget, num_cliques, clique_size_range
                );
                if max > 4.5 {
                    break;
                }
            }
        }
    }

    let core = best_graph.compute_coreness_iter_sync_opti2((1.0, 0.0), &mut archi, true);
    write_file(core, "./core.txt").unwrap();

    best_graph.transform_to_dot_file("./random.dot");
    best_graph
        .standardize_graph("./standardized_random.txt")
        .unwrap();

    println!(
        "Numero di nodi: {}, Numero di archi: {} / {}",
        best_graph.inmap.len(),
        best_graph.inmap.iter().map(|v| v.len()).sum::<usize>(),
        nodes * (nodes - 1) / 2
    );
}
