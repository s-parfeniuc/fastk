const NODE0_CORES: [(usize, usize); 8] = [
    (0, 64),
    (16, 80),
    (32, 96),
    (48, 112),
    (8, 72),
    (24, 88),
    (40, 104),
    (56, 120),
];
const NODE1_CORES: [(usize, usize); 8] = [
    (2, 66),
    (18, 82),
    (34, 98),
    (50, 114),
    (10, 74),
    (26, 90),
    (42, 106),
    (58, 122),
];
const NODE2_CORES: [(usize, usize); 8] = [
    (4, 68),
    (20, 84),
    (36, 100),
    (52, 116),
    (12, 76),
    (28, 92),
    (44, 108),
    (60, 124),
];
const NODE3_CORES: [(usize, usize); 8] = [
    (6, 70),
    (22, 86),
    (38, 102),
    (54, 118),
    (14, 78),
    (30, 94),
    (46, 110),
    (62, 126),
];
const NODE4_CORES: [(usize, usize); 8] = [
    (1, 65),
    (17, 81),
    (33, 97),
    (49, 113),
    (9, 73),
    (25, 89),
    (41, 105),
    (57, 121),
];
const NODE5_CORES: [(usize, usize); 8] = [
    (3, 67),
    (19, 83),
    (35, 99),
    (51, 115),
    (11, 75),
    (27, 91),
    (43, 107),
    (59, 123),
];
const NODE6_CORES: [(usize, usize); 8] = [
    (5, 69),
    (21, 85),
    (37, 101),
    (53, 117),
    (13, 77),
    (29, 93),
    (45, 109),
    (61, 125),
];
const NODE7_CORES: [(usize, usize); 8] = [
    (7, 71),
    (23, 87),
    (39, 103),
    (55, 119),
    (15, 79),
    (31, 95),
    (47, 111),
    (63, 127),
];

type NumaNode = [(usize, usize); 8];

// test configuration with first 12 cores set to 0..11 and the rest to 0
const fn test() -> [usize; 128] {
    let mut out = [0; 128];
    let mut i = 0;
    while i < 12 {
        out[i] = 12 - i;
        i += 1;
    }
    out
}

pub const TEST: [usize; 128] = test();

/// Return an array of 128 usize, where the first 64 elements are the first logical cores of the nodes in cluster0 and cluster1, and the last 64 elements are the second logical cores of the nodes in cluster0 and cluster1.
const fn same_cluster_no_ht(cluster0: [&NumaNode; 4], cluster1: [&NumaNode; 4]) -> [usize; 128] {
    let mut out = [0usize; 128];
    let mut idx = 0;

    // cluster 0 – first logical cores
    let mut c = 0;
    while c < 4 {
        let mut i = 0;
        while i < 8 {
            out[idx] = cluster0[c][i].0;
            idx += 1;
            i += 1;
        }
        c += 1;
    }

    // cluster 0 – second logical cores
    c = 0;
    while c < 4 {
        let mut i = 0;
        while i < 8 {
            out[idx] = cluster0[c][i].1;
            idx += 1;
            i += 1;
        }
        c += 1;
    }

    // cluster 1 – first logical cores
    c = 0;
    while c < 4 {
        let mut i = 0;
        while i < 8 {
            out[idx] = cluster1[c][i].0;
            idx += 1;
            i += 1;
        }
        c += 1;
    }

    // cluster 1 – second logical cores
    c = 0;
    while c < 4 {
        let mut i = 0;
        while i < 8 {
            out[idx] = cluster1[c][i].1;
            idx += 1;
            i += 1;
        }
        c += 1;
    }

    out
}

pub const SAME_CLUSTER_NO_HYPERTHREADING: [usize; 128] = same_cluster_no_ht(
    [&NODE1_CORES, &NODE0_CORES, &NODE2_CORES, &NODE3_CORES],
    [&NODE5_CORES, &NODE4_CORES, &NODE6_CORES, &NODE7_CORES],
);

const fn same_cluster_ht(nodes: [&NumaNode; 8]) -> [usize; 128] {
    let mut out = [0usize; 128];
    let mut idx = 0;

    let mut n = 0;
    while n < 8 {
        let mut i = 0;
        while i < 8 {
            out[idx] = nodes[n][i].0;
            idx += 1;
            out[idx] = nodes[n][i].1;
            idx += 1;
            i += 1;
        }
        n += 1;
    }

    out
}
pub const SAME_CLUSTER_WITH_HYPERTHREADING: [usize; 128] = same_cluster_ht([
    &NODE1_CORES,
    &NODE0_CORES,
    &NODE2_CORES,
    &NODE3_CORES,
    &NODE5_CORES,
    &NODE4_CORES,
    &NODE6_CORES,
    &NODE7_CORES,
]);

const fn worst_config(first: &NumaNode, rest: [&NumaNode; 7]) -> [usize; 128] {
    let mut out = [0usize; 128];
    let mut idx = 0;

    // primo elemento
    out[idx] = first[0].0;
    idx += 1;

    let mut n = 0;
    while n < 7 {
        let mut i = 0;
        while i < 8 {
            out[idx] = rest[n][i].0;
            idx += 1;
            out[idx] = rest[n][i].1;
            idx += 1;
            i += 1;
        }
        n += 1;
    }

    // rimanenti di Node1
    let mut i = 0;
    while i < 8 {
        if i != 0 {
            out[idx] = first[i].0;
            idx += 1;
        }
        out[idx] = first[i].1;
        idx += 1;
        i += 1;
    }

    out
}

pub const WORST_CONFIG: [usize; 128] = worst_config(
    &NODE1_CORES,
    [
        &NODE7_CORES,
        &NODE6_CORES,
        &NODE4_CORES,
        &NODE5_CORES,
        &NODE3_CORES,
        &NODE2_CORES,
        &NODE0_CORES,
    ],
);

/*
Architettura Titanium
Cluster 0 (Memory Node: 1):
  Node 1 (Memory):
    Cores: 8
      Core 0: (2, 66)
      Core 1: (18, 82)
      Core 2: (34, 98)
      Core 3: (50, 114)
      Core 4: (10, 74)
      Core 5: (26, 90)
      Core 6: (42, 106)
      Core 7: (58, 122)
  Node 0 (Compute):
    Cores: 8
      Core 0: (0, 64)
      Core 1: (16, 80)
      Core 2: (32, 96)
      Core 3: (48, 112)
      Core 4: (8, 72)
      Core 5: (24, 88)
      Core 6: (40, 104)
      Core 7: (56, 120)
  Node 2 (Compute):
    Cores: 8
      Core 0: (4, 68)
      Core 1: (20, 84)
      Core 2: (36, 100)
      Core 3: (52, 116)
      Core 4: (12, 76)
      Core 5: (28, 92)
      Core 6: (44, 108)
      Core 7: (60, 124)
  Node 3 (Compute):
    Cores: 8
      Core 0: (6, 70)
      Core 1: (22, 86)
      Core 2: (38, 102)
      Core 3: (54, 118)
      Core 4: (14, 78)
      Core 5: (30, 94)
      Core 6: (46, 110)
      Core 7: (62, 126)

Cluster 1 (Memory Node: 5):
  Node 5 (Memory):
    Cores: 8
      Core 0: (3, 67)
      Core 1: (19, 83)
      Core 2: (35, 99)
      Core 3: (51, 115)
      Core 4: (11, 75)
      Core 5: (27, 91)
      Core 6: (43, 107)
      Core 7: (59, 123)
  Node 4 (Compute):
    Cores: 8
      Core 0: (1, 65)
      Core 1: (17, 81)
      Core 2: (33, 97)
      Core 3: (49, 113)
      Core 4: (9, 73)
      Core 5: (25, 89)
      Core 6: (41, 105)
      Core 7: (57, 121)
  Node 6 (Compute):
    Cores: 8
      Core 0: (5, 69)
      Core 1: (21, 85)
      Core 2: (37, 101)
      Core 3: (53, 117)
      Core 4: (13, 77)
      Core 5: (29, 93)
      Core 6: (45, 109)
      Core 7: (61, 125)
  Node 7 (Compute):
    Cores: 8
      Core 0: (7, 71)
      Core 1: (23, 87)
      Core 2: (39, 103)
      Core 3: (55, 119)
      Core 4: (15, 79)
      Core 5: (31, 95)
      Core 6: (47, 111)
      Core 7: (63, 127)
*/
