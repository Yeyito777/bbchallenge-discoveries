// wt_lazy.rs: Implementation B of BB_WT.  Lazy unification search, never enumerates tile sets.
//
// Fill a DxD square cell by cell with abstract tile labels 0..n-1 (first-occurrence order).  Placing
// a label next to a placed cell forces a colour equality, kept as difunctional closure of H and V.
// Every n-tile set tiling the square follows some path in this tree with its real colours satisfying
// all forced equalities.  A node whose forced equalities already admit a periodic tiling is a leaf:
// every set below it tiles the plane.  A complete fill with no torus is a holdout.
//
// If no holdout exists at D, every n-tile set tiling DxD tiles the plane, so BB_WT(n) < D.
// Holdouts at D are the minimal sets with score >= D, or sets that need a bigger torus.
//
// Three more cuts keep the tree small; check_cert.py explains why each is sound.  A node whose state
// repeats an earlier one up to renaming is skipped.  With order "ringsym", fills that are not the
// smallest of their 8 symmetric images are skipped.  With a visit gate, a relation pair met often is
// settled outright: by a long-period torus, or as "closed" (it refuses DxD and all pairs one merge above
// it are settled).  The certificate holds only the claims, and the checkers make these decisions themselves.
//
// usage: wt_lazy N D ORDER AREA CERTPREFIX|- HOLDOUTFILE|- [RESETPOS SHARDS SHARD GATEVISITS]
use std::collections::{HashMap, HashSet};
use std::io::Write;

const MAXN: usize = 8;
type Rel = [u8; MAXN];

// multiply-rotate hasher: the keys are small structured integers and SipHash is the bottleneck otherwise
#[derive(Default, Clone, Copy)]
struct Mix(u64);
impl std::hash::Hasher for Mix {
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = (self.0.rotate_left(5) ^ *b as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
    }
    fn write_u128(&mut self, x: u128) {
        self.0 = (self.0.rotate_left(5) ^ x as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
        self.0 = (self.0.rotate_left(5) ^ (x >> 64) as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    fn finish(&self) -> u64 {
        self.0 ^ (self.0 >> 29)
    }
}
type FastHash = std::hash::BuildHasherDefault<Mix>;

fn add_edge(r: &mut Rel, n: usize, i: usize, j: usize) -> bool {
    if r[i] >> j & 1 == 1 {
        return false;
    }
    // merge the colour class of E_i with the colour class of W_j
    let row_i = r[i];
    let mut other: u8 = 0;
    for a in 0..n {
        if r[a] >> j & 1 == 1 {
            other = r[a];
            break;
        }
    }
    let target = row_i | other | (1u8 << j);
    for a in 0..n {
        let same_class_i = a == i || (row_i != 0 && r[a] == row_i);
        let same_class_j = other != 0 && r[a] == other;
        if same_class_i || same_class_j {
            r[a] = target;
        }
    }
    true
}

fn invert(r: &Rel, n: usize) -> Rel {
    let mut o = [0u8; MAXN];
    for i in 0..n {
        for j in 0..n {
            if r[i] >> j & 1 == 1 {
                o[j] |= 1 << i;
            }
        }
    }
    o
}

fn core(h: &Rel, v: &Rel, n: usize) -> u8 {
    let (hi, vi) = (invert(h, n), invert(v, n));
    let mut a: u8 = if n == 8 { 0xff } else { (1u8 << n) - 1 };
    loop {
        let mut b = a;
        for t in 0..n {
            if a >> t & 1 == 1 && (h[t] & a == 0 || hi[t] & a == 0 || v[t] & a == 0 || vi[t] & a == 0) {
                b &= !(1u8 << t);
            }
        }
        if b == a {
            return a;
        }
        a = b;
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Torus {
    a: u16,
    b: u16,
    s: u16,
    g: Vec<u8>,
}

// Lattice with a rows, b columns, and row a identified with row 0 shifted by s columns.
struct Lattice {
    a: usize,
    b: usize,
    s: usize,
    // for each cell in scan order, (other cell, kind) for already-placed-or-self partners:
    // kind 0: other is left of cell, 1: cell is left of other, 2: other above cell, 3: cell above other
    cons: Vec<Vec<(usize, u8)>>,
}

impl Lattice {
    fn new(a: usize, b: usize, s: usize) -> Lattice {
        let m = a * b;
        let mut cons = vec![Vec::new(); m];
        for r in 0..a {
            for c in 0..b {
                let x = r * b + c;
                let right = r * b + (c + 1) % b;
                let below = if r + 1 < a { (r + 1) * b + c } else { (c + s) % b };
                for (y, fwd, bwd) in [(right, 1u8, 0u8), (below, 3u8, 2u8)] {
                    if y <= x {
                        cons[x].push((y, fwd));
                    } else {
                        cons[y].push((x, bwd));
                    }
                }
            }
        }
        Lattice { a, b, s, cons }
    }
}

struct TorusSearch {
    lats: Vec<Lattice>,
    nodes: u64,
}

fn lattice_dfs(l: &Lattice, h: &Rel, v: &Rel, hi: &Rel, vi: &Rel, core: u8, x: usize, g: &mut Vec<u8>, budget: &mut i64) -> i32 {
    if x == g.len() {
        return 1;
    }
    *budget -= 1;
    if *budget < 0 {
        return -1;
    }
    let mut m = core;
    let mut self_cons: u8 = 0;
    for &(y, kind) in &l.cons[x] {
        if y == x {
            self_cons |= 1 << kind;
            continue;
        }
        let t = g[y] as usize;
        m &= match kind {
            0 => h[t],
            1 => hi[t],
            2 => v[t],
            _ => vi[t],
        };
    }
    while m != 0 {
        let t = m.trailing_zeros() as usize;
        m &= m - 1;
        if self_cons & 2 != 0 && h[t] >> t & 1 == 0 {
            continue;
        }
        if self_cons & 8 != 0 && v[t] >> t & 1 == 0 {
            continue;
        }
        g[x] = t as u8;
        let r = lattice_dfs(l, h, v, hi, vi, core, x + 1, g, budget);
        if r != 0 {
            return r;
        }
    }
    0
}

fn verify_torus(t: &Torus, h: &Rel, v: &Rel) -> bool {
    let (a, b, s) = (t.a as usize, t.b as usize, t.s as usize);
    for r in 0..a {
        for c in 0..b {
            let x = t.g[r * b + c] as usize;
            let right = t.g[r * b + (c + 1) % b] as usize;
            let below = if r + 1 < a { t.g[(r + 1) * b + c] } else { t.g[(c + s) % b] } as usize;
            if h[x] >> right & 1 == 0 || v[x] >> below & 1 == 0 {
                return false;
            }
        }
    }
    true
}

impl TorusSearch {
    fn new(max_area: usize) -> TorusSearch {
        let mut lats = Vec::new();
        for area in 1..=max_area {
            for a in 1..=area {
                if area % a == 0 {
                    let b = area / a;
                    for s in 0..b {
                        lats.push(Lattice::new(a, b, s));
                    }
                }
            }
        }
        TorusSearch { lats, nodes: 0 }
    }
    fn find(&mut self, h: &Rel, v: &Rel, n: usize, node_budget: i64) -> Option<Torus> {
        let c = core(h, v, n);
        if c == 0 {
            return None;
        }
        let (hi, vi) = (invert(h, n), invert(v, n));
        for l in &self.lats {
            let mut g = vec![0u8; l.a * l.b];
            let mut b = node_budget;
            let r = lattice_dfs(l, h, v, &hi, &vi, c, 0, &mut g, &mut b);
            self.nodes += (node_budget - b) as u64;
            if r == 1 {
                let t = Torus { a: l.a as u16, b: l.b as u16, s: l.s as u16, g };
                assert!(verify_torus(&t, h, v), "torus verification failed");
                return Some(t);
            }
        }
        None
    }
}

// Periodic rows: closed walks of length b in `along`, one row may sit below another if `down` allows it
// column by column.  Delete rows without a surviving successor until stable; any row left starts an
// infinite path through a finite graph, so a cycle of rows exists, which is an a x b torus.
fn cylinder_rows(along: &Rel, down: &Rel, core: u8, b: usize, cap: usize) -> Option<Vec<Vec<u8>>> {
    // a row is packed into a u64, 3 bits per cell, so b <= 21
    fn gen(along: &Rel, core: u8, b: usize, i: usize, first: usize, prev: usize, key: u64, out: &mut Vec<u64>, cap: usize) -> bool {
        if i == b {
            if along[prev] >> first & 1 == 1 {
                out.push(key);
            }
            return out.len() <= cap;
        }
        let mut m = if i > 0 { core & along[prev] } else { core };
        while m != 0 {
            let t = m.trailing_zeros() as usize;
            m &= m - 1;
            if !gen(along, core, b, i + 1, if i > 0 { first } else { t }, t, key | (t as u64) << (3 * i), out, cap) {
                return false;
            }
        }
        true
    }
    #[allow(clippy::too_many_arguments)]
    fn succ(along: &Rel, down: &Rel, core: u8, b: usize, from: u64, i: usize, first: usize, prev: usize, key: u64, alive: &HashSet<u64, FastHash>, work: &mut i64) -> Option<u64> {
        *work -= 1;
        if *work < 0 {
            return None;
        }
        if i == b {
            if along[prev] >> first & 1 == 1 && alive.contains(&key) {
                return Some(key);
            }
            return None;
        }
        let mut m = core & down[(from >> (3 * i) & 7) as usize];
        if i > 0 {
            m &= along[prev];
        }
        while m != 0 {
            let t = m.trailing_zeros() as usize;
            m &= m - 1;
            let r = succ(along, down, core, b, from, i + 1, if i > 0 { first } else { t }, t, key | (t as u64) << (3 * i), alive, work);
            if r.is_some() {
                return r;
            }
        }
        None
    }
    let mut rows = Vec::new();
    if !gen(along, core, b, 0, 0, 0, 0, &mut rows, cap) {
        return None;
    }
    let mut alive: HashSet<u64, FastHash> = rows.iter().cloned().collect();
    let mut work: i64 = 200_000_000;
    loop {
        let mut changed = false;
        for &r in &rows {
            if !alive.contains(&r) {
                continue;
            }
            if succ(along, down, core, b, r, 0, 0, 0, 0, &alive, &mut work).is_none() {
                if work < 0 {
                    return None;
                }
                alive.remove(&r);
                changed = true;
            }
        }
        if !changed || alive.is_empty() {
            break;
        }
    }
    let mut cur = *rows.iter().find(|r| alive.contains(*r))?;
    let mut path: Vec<u64> = Vec::new();
    loop {
        if let Some(i) = path.iter().position(|p| *p == cur) {
            return Some(path[i..].iter().map(|r| (0..b).map(|c| (r >> (3 * c) & 7) as u8).collect()).collect());
        }
        path.push(cur);
        let mut w = i64::MAX;
        cur = succ(along, down, core, b, cur, 0, 0, 0, 0, &alive, &mut w).expect("alive row has an alive successor");
    }
}

fn cylinder_torus(h: &Rel, v: &Rel, n: usize, maxb: usize) -> Option<Torus> {
    let c = core(h, v, n);
    if c == 0 {
        return None;
    }
    for b in 1..=maxb {
        if let Some(rows) = cylinder_rows(h, v, c, b, 300_000) {
            let a = rows.len();
            let g: Vec<u8> = rows.iter().flatten().cloned().collect();
            return Some(Torus { a: a as u16, b: b as u16, s: 0, g });
        }
        if let Some(cols) = cylinder_rows(v, h, c, b, 300_000) {
            let w = cols.len();
            let mut g = vec![0u8; w * b];
            for (x, col) in cols.iter().enumerate() {
                for (y, &t) in col.iter().enumerate() {
                    g[y * w + x] = t;
                }
            }
            return Some(Torus { a: b as u16, b: w as u16, s: 0, g });
        }
    }
    None
}

// Exact square test: arc consistency on tile-mask domains, branch on the smallest domain.
// Some(true) tiles, Some(false) refuses, None out of budget.
struct SquareGraph {
    d: usize,
    nb: Vec<Vec<(usize, u8)>>,
}
impl SquareGraph {
    fn new(d: usize) -> SquareGraph {
        let mut nb = vec![Vec::new(); d * d];
        for r in 0..d {
            for c in 0..d {
                let x = r * d + c;
                if c + 1 < d { nb[x].push((x + 1, 0)); }
                if c > 0 { nb[x].push((x - 1, 1)); }
                if r + 1 < d { nb[x].push((x + d, 2)); }
                if r > 0 { nb[x].push((x - d, 3)); }
            }
        }
        SquareGraph { d, nb }
    }
}
fn image_table(r: &Rel, n: usize) -> Vec<u8> {
    let mut t = vec![0u8; 1 << n];
    for m in 1..(1usize << n) {
        t[m] = t[m & (m - 1)] | r[m.trailing_zeros() as usize];
    }
    t
}
fn ac_propagate(g: &SquareGraph, tb: &[Vec<u8>; 4], dom: &mut [u8], stack: &mut Vec<usize>) -> bool {
    while let Some(x) = stack.pop() {
        let dx = dom[x] as usize;
        for &(y, kind) in &g.nb[x] {
            let m = dom[y] & tb[kind as usize][dx];
            if m != dom[y] {
                if m == 0 {
                    return false;
                }
                dom[y] = m;
                stack.push(y);
            }
        }
    }
    true
}
fn ac_branch(g: &SquareGraph, tb: &[Vec<u8>; 4], dom: &[u8], budget: &mut i64) -> Option<bool> {
    *budget -= 1;
    if *budget < 0 {
        return None;
    }
    let (mut best, mut bc) = (usize::MAX, 99);
    for (x, m) in dom.iter().enumerate() {
        let c = m.count_ones();
        if c > 1 && c < bc {
            bc = c;
            best = x;
            if c == 2 {
                break;
            }
        }
    }
    if best == usize::MAX {
        return Some(true);
    }
    let mut m = dom[best];
    while m != 0 {
        let bit = m & m.wrapping_neg();
        m &= m - 1;
        let mut d2 = dom.to_vec();
        d2[best] = bit;
        let mut st = vec![best];
        if ac_propagate(g, tb, &mut d2, &mut st) {
            match ac_branch(g, tb, &d2, budget) {
                Some(true) => return Some(true),
                None => return None,
                _ => {}
            }
        }
    }
    Some(false)
}
fn square_fill(h: &Rel, v: &Rel, n: usize, g: &SquareGraph, limit: i64) -> Option<bool> {
    let tb = [image_table(h, n), image_table(&invert(h, n), n), image_table(v, n), image_table(&invert(v, n), n)];
    let all = if n == 8 { 0xff } else { (1u8 << n) - 1 };
    let mut dom = vec![all; g.d * g.d];
    let mut st: Vec<usize> = (0..dom.len()).collect();
    if !ac_propagate(g, &tb, &mut dom, &mut st) {
        return Some(false);
    }
    let mut b = limit;
    ac_branch(g, &tb, &dom, &mut b)
}

// every relation pair one colour merge above (h,v), deduplicated, in a fixed order that the checkers repeat
fn covers(h: &Rel, v: &Rel, n: usize) -> Vec<(Rel, Rel)> {
    let mut out = Vec::new();
    let mut done: HashSet<u128, FastHash> = HashSet::default();
    for i in 0..n {
        for j in 0..n {
            if h[i] >> j & 1 == 0 {
                let mut h2 = *h;
                add_edge(&mut h2, n, i, j);
                if done.insert(pack(&h2, v)) {
                    out.push((h2, *v));
                }
            }
        }
    }
    for i in 0..n {
        for j in 0..n {
            if v[i] >> j & 1 == 0 {
                let mut v2 = *v;
                add_edge(&mut v2, n, i, j);
                if done.insert(pack(h, &v2)) {
                    out.push((*h, v2));
                }
            }
        }
    }
    out
}

const NONE: i32 = -1;
const CLOSED: i32 = -2;
fn encode(x: i32) -> u32 {
    match x {
        NONE => 0,
        CLOSED => 1,
        id => id as u32 + 2,
    }
}

fn make_order(d: usize, kind: &str) -> Vec<(usize, usize)> {
    let mut o = Vec::new();
    match kind {
        "scan" => {
            for r in 0..d {
                for c in 0..d {
                    o.push((r, c));
                }
            }
        }
        "shell" => {
            for k in 0..d {
                for r in 0..k {
                    o.push((r, k));
                }
                for c in 0..=k {
                    o.push((k, c));
                }
            }
        }
        "ring" | "ringsym" => {
            // centred: 1x1 or 2x2 core, then square rings clockwise, so all 8 symmetries keep the prefix shape
            let start = if d % 2 == 1 { d / 2 } else { d / 2 - 1 };
            let (mut lo, mut hi) = (start, if d % 2 == 1 { d / 2 } else { d / 2 });
            loop {
                if lo == hi {
                    o.push((lo, lo));
                } else {
                    for c in lo..hi {
                        o.push((lo, c));
                    }
                    for r in lo..hi {
                        o.push((r, hi));
                    }
                    for c in (lo + 1..=hi).rev() {
                        o.push((hi, c));
                    }
                    for r in (lo + 1..=hi).rev() {
                        o.push((r, lo));
                    }
                }
                if lo == 0 {
                    break;
                }
                lo -= 1;
                hi += 1;
            }
        }
        _ => panic!("unknown order"),
    }
    assert!(o.len() == d * d);
    o
}

// For each of the 7 non-identity symmetries of the square: image[g][i] = fill position of the cell that
// the symmetry sends to order[i].  Reading labels through this gives the symmetric fill of the same set
// under the matching reflected or transposed colours.
fn symmetry_tables(order: &[(usize, usize)], d: usize) -> Vec<Vec<usize>> {
    let mut index = vec![vec![0usize; d]; d];
    for (i, &(r, c)) in order.iter().enumerate() {
        index[r][c] = i;
    }
    let m = d - 1;
    let maps: [fn(usize, usize, usize) -> (usize, usize); 7] = [
        |r, c, m| (r, m - c),
        |r, c, m| (m - r, c),
        |r, c, m| (m - r, m - c),
        |r, c, _| (c, r),
        |r, c, m| (c, m - r),
        |r, c, m| (m - c, r),
        |r, c, m| (m - c, m - r),
    ];
    maps.iter().map(|f| order.iter().map(|&(r, c)| { let (a, b) = f(r, c, m); index[a][b] }).collect()).collect()
}

fn pack(h: &Rel, v: &Rel) -> u128 {
    let mut x: u128 = 0;
    for i in 0..MAXN {
        x |= (h[i] as u128) << (8 * i);
        x |= (v[i] as u128) << (64 + 8 * i);
    }
    x
}

struct Search {
    n: usize,
    d: usize,
    order: Vec<(usize, usize)>,
    frontier: Vec<Vec<usize>>, // for each pos: order indices (< pos) that still touch an unplaced cell
    nbrs: Vec<[Option<usize>; 4]>, // for each pos: order index of placed left/right/up/down neighbour
    small: TorusSearch,
    mid: TorusSearch,
    cache: HashMap<u128, i32, FastHash>, // relation pair -> torus id or -1
    final_cache: HashMap<u128, i32, FastHash>,
    tori: Vec<Torus>,
    torus_ids: HashMap<Torus, u32>,
    tokens: Option<std::io::BufWriter<std::fs::File>>,
    sym: Vec<Vec<usize>>,
    use_sym: bool,
    reset_pos: usize,
    no_small: HashSet<u128, FastHash>,
    no_big: HashSet<u128, FastHash>,
    big_cache: HashMap<u128, i32, FastHash>,
    refuse_cache: HashMap<u128, bool, FastHash>,
    gate_visits: u32,
    visits: HashMap<u128, u32, FastHash>,
    gate: HashMap<u128, i32, FastHash>,
    spec: HashMap<u128, i32, FastHash>,
    spec_left: i64,
    spec_out: bool,
    spec_budget: i64,
    square: SquareGraph,
    next_square: SquareGraph,
    counter: u64,
    shards: u64,
    shard: u64,
    seen: HashSet<(u128, u128, u128), FastHash>,
    memo_hits: u64,
    tokens_bytes: u64,
    nodes: u64,
    leaves: u64,
    holdouts: Vec<(Rel, Rel, Vec<u8>)>,
    holdout_seen: HashSet<u128>,
    labels: Vec<u8>,
}

impl Search {
    fn token(&mut self, mut x: u32) {
        let w = match self.tokens.as_mut() {
            Some(w) => w,
            None => return,
        };
        loop {
            let b = (x & 0x7f) as u8;
            x >>= 7;
            self.tokens_bytes += 1;
            if x == 0 {
                w.write_all(&[b]).unwrap();
                return;
            }
            w.write_all(&[b | 0x80]).unwrap();
        }
    }
    fn torus_id(&mut self, t: Torus) -> i32 {
        if let Some(&i) = self.torus_ids.get(&t) {
            return i as i32;
        }
        let i = self.tori.len() as u32;
        self.tori.push(t.clone());
        self.torus_ids.insert(t, i);
        i as i32
    }
    // A complete fill with no small torus: a real holdout, or a set that needs a bigger torus.
    // The sweep over all small lattices is slow only when it fails, so failures are remembered up to a
    // renaming of labels.  This only saves time: a skipped sweep just means no torus is claimed here.
    fn small_torus(&mut self, h: &Rel, v: &Rel) -> i32 {
        let key = renamed_pair(h, v, self.n);
        if self.no_small.contains(&key) {
            return NONE;
        }
        match self.small.find(h, v, self.n, 50_000) {
            Some(t) => self.torus_id(t),
            None => {
                self.no_small.insert(key);
                NONE
            }
        }
    }
    // Long-period torus search and square refusal are the expensive steps and the same pairs return in
    // every subtree, so these two caches outlive the per-subtree reset.  They only save time.
    fn big_torus(&mut self, h: &Rel, v: &Rel) -> i32 {
        let key = pack(h, v);
        if let Some(&x) = self.big_cache.get(&key) {
            return x;
        }
        let renamed = renamed_pair(h, v, self.n);
        let x = if self.no_big.contains(&renamed) {
            NONE
        } else {
            let found = match cylinder_torus(h, v, self.n, 18) {
                Some(t) => Some(t),
                None => self.mid.find(h, v, self.n, 200_000),
            };
            match found {
                Some(t) => {
                    assert!(verify_torus(&t, h, v), "torus verification failed");
                    self.torus_id(t)
                }
                None => {
                    self.no_big.insert(renamed);
                    NONE
                }
            }
        };
        self.big_cache.insert(key, x);
        x
    }
    fn refuses_square(&mut self, h: &Rel, v: &Rel) -> bool {
        let key = renamed_pair(h, v, self.n);
        if let Some(&x) = self.refuse_cache.get(&key) {
            return x;
        }
        let x = square_fill(h, v, self.n, &self.square, 200_000) == Some(false);
        self.refuse_cache.insert(key, x);
        x
    }
    fn final_torus(&mut self, h: &Rel, v: &Rel) -> i32 {
        // Refusing the next square settles it cheaply when it does; otherwise look for a torus.
        if square_fill(h, v, self.n, &self.next_square, 200_000) != Some(false) {
            return self.big_torus(h, v);
        }
        NONE
    }
    // ---- closure: (h,v) refuses DxD and every relation pair one merge above it is settled, so no set with
    // these equalities can tile DxD and fail to tile the plane.  Tried speculatively, tokens written only
    // once it succeeds.
    fn cover_ok(&mut self, h: &Rel, v: &Rel) -> bool {
        let key = pack(h, v);
        match self.cache.get(&key) {
            Some(&x) if x != NONE => return true,
            Some(_) => {
                if let Some(&y) = self.gate.get(&key) {
                    return y != NONE;
                }
            }
            None => {}
        }
        if let Some(&x) = self.spec.get(&key) {
            return x != NONE;
        }
        let id = self.small_torus(h, v);
        if id != NONE {
            self.spec.insert(key, id);
            return true;
        }
        self.try_closed(h, v)
    }
    fn try_closed(&mut self, h: &Rel, v: &Rel) -> bool {
        let key = pack(h, v);
        if let Some(&x) = self.spec.get(&key) {
            return x != NONE;
        }
        if self.spec_left <= 0 {
            self.spec_out = true;
            return false;
        }
        self.spec_left -= 1;
        if !self.refuses_square(h, v) {
            // It keeps filling, so closure cannot apply, but a longer-period torus may exist.
            let x = self.big_torus(h, v);
            self.spec.insert(key, x);
            return x != NONE;
        }
        for (h2, v2) in covers(h, v, self.n) {
            if !self.cover_ok(&h2, &v2) {
                if !self.spec_out {
                    self.spec.insert(key, NONE);
                }
                return false;
            }
        }
        self.spec.insert(key, CLOSED);
        true
    }
    fn emit_closed(&mut self, h: &Rel, v: &Rel) {
        for (h2, v2) in covers(h, v, self.n) {
            let key = pack(&h2, &v2);
            match self.cache.get(&key).copied() {
                None => {
                    let x = self.spec[&key];
                    self.cache.insert(key, x);
                    self.token(encode(x));
                    if x == CLOSED {
                        self.emit_closed(&h2, &v2);
                    }
                }
                Some(NONE) => {
                    if !self.gate.contains_key(&key) {
                        let x = self.spec[&key];
                        self.gate.insert(key, x);
                        self.token(encode(x));
                        if x == CLOSED {
                            self.emit_closed(&h2, &v2);
                        }
                    }
                }
                Some(_) => {}
            }
        }
    }
    // Lex-leader: a fill is kept only if no symmetric image, relabelled by first occurrence, reads
    // smaller along the fill order.  A partial fill is compared up to the first unplaced image cell.
    fn not_leader(&self, pos: usize) -> bool {
        for img in &self.sym {
            let mut map = [255u8; MAXN];
            let mut next = 0u8;
            for i in 0..pos {
                let q = img[i];
                if q >= pos {
                    break;
                }
                let l = self.labels[q] as usize;
                if map[l] == 255 {
                    map[l] = next;
                    next += 1;
                }
                if map[l] < self.labels[i] {
                    return true;
                }
                if map[l] > self.labels[i] {
                    break;
                }
            }
        }
        false
    }
    fn clear_caches(&mut self) {
        self.cache.clear();
        self.final_cache.clear();
        self.seen.clear();
        self.gate.clear();
        self.spec.clear();
        self.visits.clear();
    }
    fn go(&mut self, pos: usize, k: usize, h: Rel, v: Rel) {
        if self.use_sym && self.not_leader(pos) {
            return;
        }
        if pos == self.reset_pos {
            // Caches live per subtree at this depth, which bounds memory and lets shards run apart.
            self.clear_caches();
            self.counter += 1;
            if self.counter % self.shards == self.shard {
                self.node(pos, k, h, v);
                self.clear_caches();
                eprintln!("subtree counter={} nodes={} leaves={} tori={} holdouts={} bytes={}", self.counter, self.nodes, self.leaves, self.tori.len(), self.holdouts.len(), self.tokens_bytes);
            }
            return;
        }
        self.node(pos, k, h, v);
    }
    fn node(&mut self, pos: usize, k: usize, h: Rel, v: Rel) {
        let rel = pack(&h, &v);
        self.nodes += 1;
        if self.nodes % 100_000_000 == 0 {
            eprintln!("nodes={} memo_hits={} leaves={} tori={} rel_cache={} seen={} counter={} holdouts={} bytes={}", self.nodes, self.memo_hits, self.leaves, self.tori.len(), self.cache.len(), self.seen.len(), self.counter, self.holdouts.len(), self.tokens_bytes);
        }
        // A relation pair gets one token at its first visit: 0, or 1 for closed, or torus id + 2.
        let mut id = match self.cache.get(&rel) {
            Some(&x) => x,
            None => {
                let x = self.small_torus(&h, &v);
                self.cache.insert(rel, x);
                self.token(encode(x));
                x
            }
        };
        // A relation pair visited `gate_visits` times gets one more token, after trying closure.  This
        // catches the pairs with many fills, whose subtrees are large and repeat one another.
        if id == NONE {
            let count = self.visits.entry(rel).or_insert(0);
            *count += 1;
            let due = *count >= self.gate_visits;
            id = match self.gate.get(&rel) {
                Some(&x) => x,
                None if due => {
                    self.spec_left = self.spec_budget;
                    self.spec_out = false;
                    let x = if self.try_closed(&h, &v) { self.spec[&rel] } else { NONE };
                    self.gate.insert(rel, x);
                    self.token(encode(x));
                    if x == CLOSED {
                        self.emit_closed(&h, &v);
                    }
                    x
                }
                None => NONE,
            };
        }
        // At a complete fill, one more token for a relation pair still unsettled.
        if id == NONE && pos == self.d * self.d {
            id = match self.final_cache.get(&rel) {
                Some(&x) => x,
                None => {
                    let x = self.final_torus(&h, &v);
                    self.final_cache.insert(rel, x);
                    self.token(encode(x));
                    x
                }
            };
            if id == NONE && self.holdout_seen.insert(rel) {
                eprintln!("HOLDOUT H {} V {} labels {}", hex_rel(&h, self.n), hex_rel(&v, self.n), self.labels.iter().map(|x| x.to_string()).collect::<String>());
                self.holdouts.push((h, v, self.labels.clone()));
            }
        }
        if id != NONE {
            self.leaves += 1;
            return;
        }
        if pos == self.d * self.d {
            return;
        }
        // Two nodes at one position whose (labels used, frontier labels, relations) agree after renaming
        // labels have the same subtree up to that renaming, so only the first is walked.  The renaming
        // needs to be a permutation fixing the unused labels and nothing more; see state_key.
        let key = state_key(pos, k, self.n, &self.frontier[pos], &self.labels, &h, &v);
        if !self.seen.insert(key) {
            self.memo_hits += 1;
            return;
        }
        let nb = self.nbrs[pos];
        for t in 0..=k.min(self.n - 1) {
            let (mut h2, mut v2) = (h, v);
            if let Some(q) = nb[0] {
                add_edge(&mut h2, self.n, self.labels[q] as usize, t);
            }
            if let Some(q) = nb[1] {
                add_edge(&mut h2, self.n, t, self.labels[q] as usize);
            }
            if let Some(q) = nb[2] {
                add_edge(&mut v2, self.n, self.labels[q] as usize, t);
            }
            if let Some(q) = nb[3] {
                add_edge(&mut v2, self.n, t, self.labels[q] as usize);
            }
            self.labels[pos] = t as u8;
            self.go(pos + 1, if t == k { k + 1 } else { k }, h2, v2);
        }
    }
}

// Rename labels: frontier labels by first appearance, then the other used labels sorted by a signature
// (ties keep label order), unused labels unchanged.  Returns (renamed relations, position+k+frontier).
fn state_key(pos: usize, k: usize, n: usize, frontier: &[usize], labels: &[u8], h: &Rel, v: &Rel) -> (u128, u128, u128) {
    let mut map = [255u8; MAXN];
    let mut next = 0u8;
    let mut fk: [u128; 2] = [(pos as u128) | ((k as u128) << 10), 0];
    let mut sh = 14;
    for &q in frontier {
        let l = labels[q] as usize;
        if map[l] == 255 {
            map[l] = next;
            next += 1;
        }
        fk[sh / 128] |= (map[l] as u128) << (sh % 128);
        sh += 3;
        if sh % 128 > 125 {
            sh += 128 - sh % 128;
        }
    }
    assert!(sh <= 256, "frontier key too long");
    let (hi, vi) = (invert(h, n), invert(v, n));
    let mut known: u8 = 0;
    for l in 0..k {
        if map[l] != 255 {
            known |= 1 << l;
        }
    }
    let rename_known = |m: u8| -> u64 {
        let mut o = 0u64;
        let mut x = m & known;
        while x != 0 {
            let j = x.trailing_zeros() as usize;
            x &= x - 1;
            o |= 1 << map[j];
        }
        o
    };
    let mut rest: Vec<(u64, usize)> = Vec::with_capacity(MAXN);
    for l in 0..k {
        if map[l] == 255 {
            let sig = rename_known(h[l])
                | rename_known(hi[l]) << 8
                | rename_known(v[l]) << 16
                | rename_known(vi[l]) << 24
                | (h[l].count_ones() as u64) << 32
                | (hi[l].count_ones() as u64) << 36
                | (v[l].count_ones() as u64) << 40
                | (vi[l].count_ones() as u64) << 44;
            rest.push((sig, l));
        }
    }
    rest.sort();
    for &(_, l) in &rest {
        map[l] = next;
        next += 1;
    }
    for l in k..n {
        map[l] = l as u8;
    }
    let (mut h2, mut v2) = ([0u8; MAXN], [0u8; MAXN]);
    for i in 0..n {
        let (mi, mut a, mut b) = (map[i] as usize, h[i], v[i]);
        while a != 0 {
            h2[mi] |= 1 << map[a.trailing_zeros() as usize];
            a &= a - 1;
        }
        while b != 0 {
            v2[mi] |= 1 << map[b.trailing_zeros() as usize];
            b &= b - 1;
        }
    }
    (pack(&h2, &v2), fk[0], fk[1])
}

// (h,v) with labels sorted by degree signature, ties in label order: equal results mean isomorphic pairs
fn renamed_pair(h: &Rel, v: &Rel, n: usize) -> u128 {
    let (hi, vi) = (invert(h, n), invert(v, n));
    let mut sig = [(0u32, 0usize); MAXN];
    for l in 0..n {
        let deg = |m: u8, rows: &Rel| -> u32 {
            let (mut x, mut s) = (m, 0);
            while x != 0 {
                s += rows[x.trailing_zeros() as usize].count_ones();
                x &= x - 1;
            }
            s
        };
        let a = h[l].count_ones() | hi[l].count_ones() << 4 | v[l].count_ones() << 8 | vi[l].count_ones() << 12;
        let b = deg(h[l], v) + 7 * deg(v[l], h) + 49 * deg(hi[l], &vi) + 343 * deg(vi[l], &hi);
        sig[l] = ((a << 16) | (b & 0xffff), l);
    }
    sig[..n].sort();
    let mut map = [0u8; MAXN];
    for (i, &(_, l)) in sig[..n].iter().enumerate() {
        map[l] = i as u8;
    }
    let (mut h2, mut v2) = ([0u8; MAXN], [0u8; MAXN]);
    for i in 0..n {
        let (mi, mut a, mut b) = (map[i] as usize, h[i], v[i]);
        while a != 0 {
            h2[mi] |= 1 << map[a.trailing_zeros() as usize];
            a &= a - 1;
        }
        while b != 0 {
            v2[mi] |= 1 << map[b.trailing_zeros() as usize];
            b &= b - 1;
        }
    }
    pack(&h2, &v2)
}

fn hex_rel(r: &Rel, n: usize) -> String {
    (0..n).map(|i| format!("{:x}", r[i])).collect::<Vec<_>>().join(",")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let d: usize = args[2].parse().unwrap();
    let kind = args[3].clone();
    let area: usize = args[4].parse().unwrap();
    let cert = args[5].clone();
    let reset_pos: usize = if args.len() > 7 && args[7] != "0" { args[7].parse().unwrap() } else { usize::MAX };
    let shards: u64 = if args.len() > 8 { args[8].parse().unwrap() } else { 1 };
    let shard: u64 = if args.len() > 9 { args[9].parse().unwrap() } else { 0 };
    let gate_visits: u32 = if args.len() > 10 { args[10].parse().unwrap() } else { u32::MAX };
    let order = make_order(d, &kind);
    let mut index = vec![vec![usize::MAX; d]; d];
    for (i, &(r, c)) in order.iter().enumerate() {
        index[r][c] = i;
    }
    let mut frontier = Vec::new();
    let mut nbrs = Vec::new();
    for pos in 0..=d * d {
        let mut f = Vec::new();
        for q in 0..pos {
            let (r, c) = order[q];
            let mut open = false;
            if c > 0 && index[r][c - 1] >= pos { open = true; }
            if c + 1 < d && index[r][c + 1] >= pos { open = true; }
            if r > 0 && index[r - 1][c] >= pos { open = true; }
            if r + 1 < d && index[r + 1][c] >= pos { open = true; }
            if open {
                f.push(q);
            }
        }
        frontier.push(f);
        if pos < d * d {
            let (r, c) = order[pos];
            let get = |ok: bool, a: usize, b: usize| if ok && index[a][b] < pos { Some(index[a][b]) } else { None };
            nbrs.push([
                if c > 0 { get(true, r, c - 1) } else { None },
                if c + 1 < d { get(true, r, c + 1) } else { None },
                if r > 0 { get(true, r - 1, c) } else { None },
                if r + 1 < d { get(true, r + 1, c) } else { None },
            ]);
        }
    }
    let sym = symmetry_tables(&order, d);
    let mut s = Search {
        sym,
        use_sym: kind == "ringsym",
        reset_pos,
        no_small: HashSet::default(),
        no_big: HashSet::default(),
        big_cache: HashMap::default(),
        refuse_cache: HashMap::default(),
        gate_visits,
        visits: HashMap::default(),
        gate: HashMap::default(),
        spec: HashMap::default(),
        spec_left: 0,
        spec_out: false,
        spec_budget: 3000,
        square: SquareGraph::new(d),
        next_square: SquareGraph::new(d + 1),
        counter: 0,
        shards,
        shard,
        seen: HashSet::default(),
        memo_hits: 0,
        n,
        d,
        order,
        frontier,
        nbrs,
        small: TorusSearch::new(area),
        mid: TorusSearch::new(40),
        cache: HashMap::default(),
        final_cache: HashMap::default(),
        tori: Vec::new(),
        torus_ids: HashMap::new(),
        tokens: if cert != "-" { Some(std::io::BufWriter::new(std::fs::File::create(format!("{}.tree", cert)).unwrap())) } else { None },
        tokens_bytes: 0,
        nodes: 0,
        leaves: 0,
        holdouts: Vec::new(),
        holdout_seen: HashSet::new(),
        labels: vec![0; d * d],
    };
    s.go(0, 0, [0; MAXN], [0; MAXN]);
    println!(
        "n={} D={} order={} area={} nodes={} memo_hits={} leaves={} tori={} holdouts={} tokens_bytes={}",
        n, d, kind, area, s.nodes, s.memo_hits, s.leaves, s.tori.len(), s.holdouts.len(), s.tokens_bytes
    );
    let _ = &s.order;
    if args.len() > 6 && args[6] != "-" {
        let mut f = std::fs::File::create(&args[6]).unwrap();
        for (h, v, labels) in &s.holdouts {
            let mut score = 0;
            let mut status = "open".to_string();
            for x in 1..=40 {
                match square_fill(h, v, n, &SquareGraph::new(x), 20_000_000) {
                    Some(true) => score = x,
                    Some(false) => {
                        status = "refused".into();
                        break;
                    }
                    None => {
                        status = "budget".into();
                        break;
                    }
                }
            }
            let row: Vec<String> = labels.iter().map(|x| x.to_string()).collect();
            writeln!(f, "holdout H {} V {} fills_upto {} {} labels {}", hex_rel(h, n), hex_rel(v, n), score, status, row.join("")).unwrap();
        }
    }
    if cert != "-" {
        let mut f = std::fs::File::create(format!("{}.tori", cert)).unwrap();
        writeln!(f, "wt-cert 3 n {} D {} order {} tori {} reset {} shards {} shard {} gate {}", n, d, kind, s.tori.len(), if reset_pos == usize::MAX { 0 } else { reset_pos }, shards, shard, if gate_visits == u32::MAX { 0 } else { gate_visits }).unwrap();
        for t in &s.tori {
            let g: Vec<String> = t.g.iter().map(|x| x.to_string()).collect();
            writeln!(f, "{} {} {} {}", t.a, t.b, t.s, g.join(" ")).unwrap();
        }
        s.tokens.as_mut().unwrap().flush().unwrap();
    }
}
