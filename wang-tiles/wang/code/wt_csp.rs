// wt_csp.rs: Implementation C of BB_WT, a cross-check of the full score histogram.
//
// Shares no code or method with wt_pairs.c beyond the definitions:
//   relations come from walking every colouring of the 2n ends and deduplicating;
//   relation classes come from union-find under adjacent transpositions and transpose;
//   squares and lattice tori are solved by arc consistency with smallest-domain branching.
//
// usage: wt_csp N OUTDIR THREADS [SOFTCAP]
// Output files have the same format as wt_pairs, so aggregate.py reads both.
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

const NMAX: usize = 7;
type Rel = [u8; NMAX];

fn all_relations(n: usize) -> Vec<Rel> {
    fn rec(n: usize, pos: usize, used: u8, col: &mut [u8; 2 * NMAX], out: &mut HashSet<Rel>) {
        if pos == 2 * n {
            let mut r = [0u8; NMAX];
            for i in 0..n {
                for j in 0..n {
                    if col[i] == col[n + j] {
                        r[i] |= 1 << j;
                    }
                }
            }
            out.insert(r);
            return;
        }
        for c in 0..=used {
            col[pos] = c;
            rec(n, pos + 1, if c == used { used + 1 } else { used }, col, out);
        }
    }
    let mut set = HashSet::new();
    rec(n, 0, 0, &mut [0; 2 * NMAX], &mut set);
    let mut v: Vec<Rel> = set.into_iter().collect();
    v.sort();
    v
}

fn transpose(r: &Rel, n: usize) -> Rel {
    let mut o = [0u8; NMAX];
    for i in 0..n {
        for j in 0..n {
            if r[i] >> j & 1 == 1 {
                o[j] |= 1 << i;
            }
        }
    }
    o
}

fn swap_labels(r: &Rel, n: usize, a: usize, b: usize) -> Rel {
    let f = |x: usize| if x == a { b } else if x == b { a } else { x };
    let mut o = [0u8; NMAX];
    for i in 0..n {
        for j in 0..n {
            if r[i] >> j & 1 == 1 {
                o[f(i)] |= 1 << f(j);
            }
        }
    }
    o
}

fn uf_find(p: &mut Vec<u32>, mut x: u32) -> u32 {
    while p[x as usize] != x {
        let g = p[p[x as usize] as usize];
        p[x as usize] = g;
        x = g;
    }
    x
}

// One constraint graph: a square or a lattice torus. nb[x] holds up to 4 (neighbour, kind),
// kind 0: neighbour is right of x, 1: left of x, 2: below x, 3: above x
struct Graph {
    size: usize,
    nb: Vec<[(u16, u8); 4]>,
    deg: Vec<u8>,
}

fn square_graph(d: usize) -> Graph {
    let mut g = Graph { size: d * d, nb: vec![[(0, 0); 4]; d * d], deg: vec![0; d * d] };
    for r in 0..d {
        for c in 0..d {
            let x = r * d + c;
            let mut k = 0;
            for &(ok, y, kind) in &[
                (c + 1 < d, x + 1, 0u8),
                (c > 0, x.wrapping_sub(1), 1),
                (r + 1 < d, x + d, 2),
                (r > 0, x.wrapping_sub(d), 3),
            ] {
                if ok {
                    g.nb[x][k] = (y as u16, kind);
                    k += 1;
                }
            }
            g.deg[x] = k as u8;
        }
    }
    g
}

fn lattice_graph(a: usize, b: usize, s: usize) -> Graph {
    let m = a * b;
    let mut g = Graph { size: m, nb: vec![[(0, 0); 4]; m], deg: vec![4; m] };
    for r in 0..a {
        for c in 0..b {
            let x = r * b + c;
            let right = r * b + (c + 1) % b;
            let below = if r + 1 < a { (r + 1) * b + c } else { (c + s) % b };
            g.nb[x][0] = (right as u16, 0);
            g.nb[right][1] = (x as u16, 1);
            g.nb[x][2] = (below as u16, 2);
            g.nb[below][3] = (x as u16, 3);
        }
    }
    g
}

struct Tables {
    // tab[kind][tile mask] = union of tiles allowed in the neighbour of that kind
    tab: [Vec<u8>; 4],
}

fn image_table(r: &Rel, n: usize) -> Vec<u8> {
    let mut t = vec![0u8; 1 << n];
    for m in 1..(1usize << n) {
        let low = m.trailing_zeros() as usize;
        t[m] = t[m & (m - 1)] | r[low];
    }
    t
}

fn propagate(g: &Graph, tb: &Tables, dom: &mut [u8], stack: &mut Vec<u16>) -> bool {
    while let Some(x) = stack.pop() {
        let x = x as usize;
        let dx = dom[x] as usize;
        for k in 0..g.deg[x] as usize {
            let (y, kind) = g.nb[x][k];
            let y = y as usize;
            let m = dom[y] & tb.tab[kind as usize][dx];
            if m != dom[y] {
                if m == 0 {
                    return false;
                }
                dom[y] = m;
                stack.push(y as u16);
            }
        }
    }
    true
}

fn branch(g: &Graph, tb: &Tables, dom: &mut Vec<u8>, stack: &mut Vec<u16>, budget: &mut i64) -> i32 {
    *budget -= 1;
    if *budget < 0 {
        return -1;
    }
    let mut best = usize::MAX;
    let mut bc = 99;
    for x in 0..g.size {
        let c = dom[x].count_ones();
        if c > 1 && c < bc {
            bc = c;
            best = x;
            if c == 2 {
                break;
            }
        }
    }
    if best == usize::MAX {
        return 1;
    }
    let mut m = dom[best];
    while m != 0 {
        let bit = m & m.wrapping_neg();
        m &= m - 1;
        let mut d2 = dom.clone();
        d2[best] = bit;
        stack.clear();
        stack.push(best as u16);
        if propagate(g, tb, &mut d2, stack) {
            let r = branch(g, tb, &mut d2, stack, budget);
            if r == 1 {
                *dom = d2;
                return 1;
            }
            if r < 0 {
                return -1;
            }
        }
    }
    0
}

fn solve(g: &Graph, tb: &Tables, n: usize, budget: i64) -> (i32, Vec<u8>) {
    let mut dom = vec![((1u32 << n) - 1) as u8; g.size];
    let mut stack: Vec<u16> = (0..g.size as u16).collect();
    if !propagate(g, tb, &mut dom, &mut stack) {
        return (0, dom);
    }
    let mut b = budget;
    let r = branch(g, tb, &mut dom, &mut stack, &mut b);
    (r, dom)
}

fn check_solution(g: &Graph, dom: &[u8], h: &Rel, v: &Rel) {
    for x in 0..g.size {
        let t = dom[x].trailing_zeros() as usize;
        assert!(dom[x].count_ones() == 1);
        for k in 0..g.deg[x] as usize {
            let (y, kind) = g.nb[x][k];
            let u = dom[y as usize].trailing_zeros() as usize;
            let ok = match kind {
                0 => h[t] >> u & 1 == 1,
                1 => h[u] >> t & 1 == 1,
                2 => v[t] >> u & 1 == 1,
                _ => v[u] >> t & 1 == 1,
            };
            assert!(ok, "solution check failed");
        }
    }
}

struct Graphs {
    squares: Vec<Graph>,
    lats: Vec<Graph>,
    quick: usize,
}

fn classify(h: &Rel, v: &Rel, himg: &[u8], himg_t: &[u8], n: usize, gs: &Graphs, softcap: usize) -> i32 {
    let tb = Tables { tab: [himg.to_vec(), himg_t.to_vec(), image_table(v, n), image_table(&transpose(v, n), n)] };
    for g in &gs.lats[..gs.quick] {
        let (r, dom) = solve(g, &tb, n, 2000);
        if r == 1 {
            check_solution(g, &dom, h, v);
            return 0;
        }
    }
    for d in 2..gs.squares.len() {
        let g = &gs.squares[d];
        let (r, dom) = solve(g, &tb, n, 20_000_000);
        if r == 0 {
            return d as i32 - 1;
        }
        if r == 1 {
            check_solution(g, &dom, h, v);
        }
        if d >= softcap || r < 0 {
            for g in &gs.lats[gs.quick..] {
                let (r, dom) = solve(g, &tb, n, 200_000);
                if r == 1 {
                    check_solution(g, &dom, h, v);
                    return 0;
                }
            }
            if r < 0 {
                return -1;
            }
        }
    }
    -1
}

fn hexrel(r: &Rel, n: usize) -> String {
    (0..n).map(|i| format!("{:x}", r[i])).collect::<Vec<_>>().join(",")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let outdir = args[2].clone();
    let threads: usize = args[3].parse().unwrap();
    let softcap: usize = if args.len() > 4 { args[4].parse().unwrap() } else { n + 2 };
    std::fs::create_dir_all(&outdir).unwrap();
    let rels = all_relations(n);
    let index: HashMap<Rel, u32> = rels.iter().enumerate().map(|(i, r)| (*r, i as u32)).collect();
    let mut p: Vec<u32> = (0..rels.len() as u32).collect();
    for (i, r) in rels.iter().enumerate() {
        let mut others = vec![transpose(r, n)];
        for a in 0..n.saturating_sub(1) {
            others.push(swap_labels(r, n, a, a + 1));
        }
        for o in others {
            let (x, y) = (uf_find(&mut p, i as u32), uf_find(&mut p, index[&o]));
            if x != y {
                p[x.max(y) as usize] = x.min(y);
            }
        }
    }
    let mut class_id: HashMap<u32, u32> = HashMap::new();
    let mut reps: Vec<u32> = Vec::new();
    let mut sizes: Vec<u64> = Vec::new();
    let mut cls = vec![0u32; rels.len()];
    for i in 0..rels.len() {
        let root = uf_find(&mut p, i as u32);
        let next = class_id.len() as u32;
        let c = *class_id.entry(root).or_insert_with(|| {
            reps.push(i as u32);
            sizes.push(0);
            next
        });
        cls[i] = c;
        sizes[c as usize] += 1;
    }
    // for class C: V list = relations of class >= C, one of each transpose pair, multiplicity kept
    let mut vs: Vec<(u32, Rel, u8)> = Vec::new();
    for (i, r) in rels.iter().enumerate() {
        let t = transpose(r, n);
        if t < *r {
            continue;
        }
        vs.push((cls[i], *r, if t == *r { 1 } else { 2 }));
    }
    vs.sort_by_key(|x| x.0);
    eprintln!("n={} relations={} classes={} vlist={}", n, rels.len(), reps.len(), vs.len());
    let mut squares = Vec::new();
    for d in 0..=30 {
        squares.push(square_graph(d));
    }
    let mut lats = Vec::new();
    let mut quick = 0;
    for area in 1..=120 {
        for a in 1..=area {
            if area % a == 0 {
                let b = area / a;
                for s in 0..b {
                    lats.push(lattice_graph(a, b, s));
                }
            }
        }
        if area == 4 {
            quick = lats.len();
        }
    }
    let shared = Arc::new((rels, reps, sizes, vs, Graphs { squares, lats, quick }, AtomicUsize::new(0)));
    let mut handles = Vec::new();
    for _ in 0..threads {
        let sh = shared.clone();
        let outdir = outdir.clone();
        handles.push(std::thread::spawn(move || {
            let (rels, reps, sizes, vs, gs, next) = (&sh.0, &sh.1, &sh.2, &sh.3, &sh.4, &sh.5);
            loop {
                let c = next.fetch_add(1, Ordering::Relaxed);
                if c >= reps.len() {
                    return;
                }
                let path = format!("{}/c{:06}.txt", outdir, c);
                if std::path::Path::new(&path).exists() {
                    continue;
                }
                let h = rels[reps[c] as usize];
                let (himg, himg_t) = (image_table(&h, n), image_table(&transpose(&h, n), n));
                let mut hist = [0u64; 32];
                let (mut plane, mut pairs, mut unres) = (0u64, 0u64, 0u64);
                let mut lines = String::new();
                let start = vs.partition_point(|x| (x.0 as usize) < c);
                for (vc, v, mult) in &vs[start..] {
                    let w = sizes[c] * (*mult as u64) * if *vc as usize == c { 1 } else { 2 };
                    pairs += 1;
                    let s = classify(&h, v, &himg, &himg_t, n, gs, softcap);
                    if s == 0 {
                        plane += w;
                    } else if s > 0 {
                        hist[s as usize] += w;
                    } else {
                        unres += w;
                        lines += &format!("unres {} H {} V {}\n", w, hexrel(&h, n), hexrel(v, n));
                    }
                }
                lines += &format!("pairs {}\nplane {}\nunresolved {}\n", pairs, plane, unres);
                for s in 1..32 {
                    if hist[s] > 0 {
                        lines += &format!("score {} {}\n", s, hist[s]);
                    }
                }
                lines += "done\n";
                let tmp = format!("{}.tmp{}", path, c);
                let mut f = std::fs::File::create(&tmp).unwrap();
                f.write_all(lines.as_bytes()).unwrap();
                drop(f);
                std::fs::rename(&tmp, &path).unwrap();
            }
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    eprintln!("finished");
}
