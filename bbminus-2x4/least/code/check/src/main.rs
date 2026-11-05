// check: independent verifier for a BB_init(2,4,T) ledger. Shares no code with tree.c, cps.c, repwl.c.
// It walks the normalised machine tree itself, from the empty machine, and demands one ledger record per node:
//   H <steps> <tm>            the machine reaches its first undefined transition on step <steps> (halting step counted)
//   C <t0> <period> <d> <tm>  Lin recurrence: from step t0, every <period> steps the config repeats shifted by d
//   P <tm> <n> <mode> <h> <presim>         annotated n-gram closed position set
//   W <tm> <L> <T> <K> <presim>            repeated word list closed graph
//   L <tm> <K> <M> <B> <OFF> <C>           closed language over run-compressed blocks (see check_runlang)
// Only a halting node has children. Every ledger record must be used exactly once.
// Simulation uses two stacks (cells left of the head, cells right of the head) with the background generated lazily.
use std::collections::{HashMap, HashSet};
use std::io::{BufRead, BufReader};

const NS: usize = 2;
const NY: usize = 4;
type Trans = [Option<(u8, bool, u8)>; NS * NY]; // write, moves right, next state

fn tm_to_string(t: &Trans) -> String {
    let mut s = String::new();
    for i in 0..NS * NY {
        if i == NY { s.push('_'); }
        match t[i] {
            None => s.push_str("---"),
            Some((w, r, n)) => { s.push((b'0' + w) as char); s.push(if r { 'R' } else { 'L' }); s.push((b'A' + n) as char); }
        }
    }
    s
}
fn parse_tm(c: &str) -> Trans {
    let b = c.as_bytes();
    assert_eq!(b.len(), NS * (3 * NY) + NS - 1, "bad tm {}", c);
    let mut t: Trans = [None; NS * NY];
    for i in 0..NS * NY {
        let o = i * 3 + i / NY;
        if b[o] != b'-' { t[i] = Some((b[o] - b'0', b[o + 1] == b'R', b[o + 2] - b'A')); }
    }
    t
}
fn key(t: &Trans) -> u64 {
    let mut k = 0u64;
    for i in 0..NS * NY {
        let v = match t[i] { None => 0u64, Some((w, r, n)) => 1 + (w as u64) * 4 + (r as u64) * 2 + n as u64 };
        k = k * 17 + v;
    }
    k
}

#[derive(Clone, Debug)]
struct Spec { lp: Vec<u8>, rp: Vec<u8>, left: Vec<u8>, head: u8, right: Vec<u8> }
fn parse_tape(s: &str) -> Spec {
    // [(LP)] left [h] right [(RP)]
    let mut lp = vec![0u8]; let mut rp = vec![0u8];
    let mut rest = s;
    if rest.starts_with('(') { let e = rest.find(')').unwrap(); lp = rest[1..e].bytes().map(|c| c - b'0').collect(); rest = &rest[e + 1..]; }
    if rest.ends_with(')') { let o = rest.rfind('(').unwrap(); rp = rest[o + 1..rest.len() - 1].bytes().map(|c| c - b'0').collect(); rest = &rest[..o]; }
    let o = rest.find('[').unwrap(); let e = rest.find(']').unwrap();
    Spec { lp, rp, left: rest[..o].bytes().map(|c| c - b'0').collect(), head: rest.as_bytes()[o + 1] - b'0', right: rest[e + 1..].bytes().map(|c| c - b'0').collect() }
}
impl Spec {
    // cell k steps away from the head on the left (k = 1 is adjacent), as in the original tape
    fn left_cell(&self, k: usize) -> u8 {
        if k <= self.left.len() { self.left[self.left.len() - k] }
        else { let j = k - self.left.len() - 1; self.lp[self.lp.len() - 1 - j % self.lp.len()] }
    }
    fn right_cell(&self, k: usize) -> u8 {
        if k <= self.right.len() { self.right[k - 1] }
        else { let j = k - self.right.len() - 1; self.rp[j % self.rp.len()] }
    }
    fn at(&self, pos: i64) -> u8 {
        if pos == 0 { self.head } else if pos < 0 { self.left_cell((-pos) as usize) } else { self.right_cell(pos as usize) }
    }
    fn symbols(&self) -> u32 {
        let mut m = 1u32 | (1 << self.head);
        for &c in self.left.iter().chain(self.right.iter()).chain(self.lp.iter()).chain(self.rp.iter()) { m |= 1 << c; }
        m
    }
}

// Two-stack machine. ls holds cells materialised on the left, ls[0] furthest. pos is the head position relative to start.
struct Run<'a> { spec: &'a Spec, ls: Vec<u8>, rs: Vec<u8>, cur: u8, pos: i64, st: u8, steps: u64, lmat: i64, rmat: i64 }
impl<'a> Run<'a> {
    fn new(spec: &'a Spec) -> Self { Run { spec, ls: Vec::new(), rs: Vec::new(), cur: spec.head, pos: 0, st: 0, steps: 0, lmat: 0, rmat: 0 } }
    // lmat/rmat: lowest and highest position ever materialised
    #[inline] fn step(&mut self, t: &Trans) -> bool { // false when undefined
        match t[self.st as usize * NY + self.cur as usize] {
            None => false,
            Some((w, r, n)) => {
                if r {
                    self.ls.push(w); self.pos += 1;
                    self.cur = match self.rs.pop() { Some(c) => c, None => { self.rmat = self.pos; self.spec.at(self.pos) } };
                } else {
                    self.rs.push(w); self.pos -= 1;
                    self.cur = match self.ls.pop() { Some(c) => c, None => { self.lmat = self.pos; self.spec.at(self.pos) } };
                }
                self.st = n; self.steps += 1; true
            }
        }
    }
    fn get(&self, p: i64) -> u8 {
        if p == self.pos { return self.cur; }
        if p < self.pos { let k = (self.pos - p) as usize; if k <= self.ls.len() { self.ls[self.ls.len() - k] } else { self.spec.at(p) } }
        else { let k = (p - self.pos) as usize; if k <= self.rs.len() { self.rs[self.rs.len() - k] } else { self.spec.at(p) } }
    }
}

fn check_lin(spec: &Spec, t: &Trans, t0: u64, per: u64, d: i64) -> Result<(), String> {
    let mut r = Run::new(spec);
    for _ in 0..t0 { if !r.step(t) { return Err("halts before t0".into()); } }
    let (st0, pos0) = (r.st, r.pos);
    let (mut lo, mut hi) = (r.pos, r.pos);
    // Lowest and highest cell that may differ from the background at t0.
    let far_lo = r.lmat.min(-(spec.left.len() as i64)) - 1; let far_hi = r.rmat.max(spec.right.len() as i64) + 1;
    let snap_ls = r.ls.clone(); let snap_rs = r.rs.clone(); let snap_cur = r.cur;
    let at0 = |p: i64| -> u8 {
        if p == pos0 { snap_cur }
        else if p < pos0 { let k = (pos0 - p) as usize; if k <= snap_ls.len() { snap_ls[snap_ls.len() - k] } else { spec.at(p) } }
        else { let k = (p - pos0) as usize; if k <= snap_rs.len() { snap_rs[snap_rs.len() - k] } else { spec.at(p) } }
    };
    for _ in 0..per { if !r.step(t) { return Err("halts inside period".into()); } lo = lo.min(r.pos); hi = hi.max(r.pos); }
    if r.st != st0 { return Err("state differs".into()); }
    if r.pos - pos0 != d { return Err("shift differs".into()); }
    for p in lo..=hi { if r.get(p + d) != at0(p) { return Err(format!("window mismatch at {}", p)); } }
    if d > 0 {
        if d % spec.rp.len() as i64 != 0 { return Err("shift not a multiple of the right period".into()); }
        for p in hi + 1..=far_hi + spec.rp.len() as i64 { if at0(p) != at0(p + d) { return Err("right tail not invariant".into()); } }
    } else if d < 0 {
        if (-d) % spec.lp.len() as i64 != 0 { return Err("shift not a multiple of the left period".into()); }
        let mut p = lo - 1; let stop = far_lo - spec.lp.len() as i64;
        while p >= stop { if at0(p) != at0(p + d) { return Err("left tail not invariant".into()); } p -= 1; }
    }
    Ok(())
}

// Annotated cell: symbol plus tag. Modes: 0 plain; 1 per-cell list of its last h (state,symbol) updates;
// 2 head carries last h transitions, copied into each written cell; 3 head carries an LRU list of h distinct transitions.
type Cell = (u8, Vec<u8>);
fn tag_push(mode: u32, h: usize, tag: &mut Vec<u8>, code: u8) {
    if mode == 3 { if let Some(i) = tag.iter().position(|&x| x == code) { tag.remove(i); } }
    tag.insert(0, code); tag.truncate(h);
}
fn check_cps(spec: &Spec, t: &Trans, n: usize, mode: u32, h: usize, presim: u64) -> Result<usize, String> {
    if presim != 0 { let mut r = Run::new(spec); for _ in 0..presim { if !r.step(t) { return Err("halt in presim".into()); } } }
    // Annotated presimulation is only supported for presim == 0 in this checker.
    if presim != 0 { return Err("presim unsupported".into()); }
    let mut cells: Vec<Cell> = Vec::new(); let mut idx: HashMap<Cell, u32> = HashMap::new();
    let mut intern = |c: Cell, cells: &mut Vec<Cell>| -> u32 { if let Some(&i) = idx.get(&c) { i } else { let i = cells.len() as u32; cells.push(c.clone()); idx.insert(c, i); i } };
    let mut gl: HashSet<Vec<u32>> = HashSet::new(); let mut gr: HashSet<Vec<u32>> = HashSet::new();
    let span = n + spec.left.len() + spec.right.len() + spec.lp.len() + spec.rp.len() + 2;
    let lc: Vec<u32> = (1..=span + n).map(|k| intern((spec.at(-(k as i64)), vec![]), &mut cells)).collect();
    let rc: Vec<u32> = (1..=span + n).map(|k| intern((spec.at(k as i64), vec![]), &mut cells)).collect();
    for i in 0..span { gl.insert(lc[i..i + n].to_vec()); gr.insert(rc[i..i + n].to_vec()); }
    // prefix index: first n-1 cells of a gram -> possible last cells
    let mut pl: HashMap<Vec<u32>, Vec<u32>> = HashMap::new(); let mut pr: HashMap<Vec<u32>, Vec<u32>> = HashMap::new();
    for g in &gl { pl.entry(g[..n - 1].to_vec()).or_default().push(g[n - 1]); }
    for g in &gr { pr.entry(g[..n - 1].to_vec()).or_default().push(g[n - 1]); }
    let c0 = intern((spec.head, vec![]), &mut cells);
    #[derive(Clone, PartialEq, Eq, Hash)]
    struct Abs { st: u8, carry: Vec<u8>, c: u32, l: Vec<u32>, r: Vec<u32> }
    let start = Abs { st: 0, carry: vec![], c: c0, l: lc[..n].to_vec(), r: rc[..n].to_vec() };
    let mut seen: HashSet<Abs> = HashSet::new(); seen.insert(start.clone());
    let mut todo = vec![start];
    // waiters: abstract configs blocked on a prefix, re-expanded when a new last cell arrives
    let mut wl: HashMap<Vec<u32>, Vec<Abs>> = HashMap::new(); let mut wr: HashMap<Vec<u32>, Vec<Abs>> = HashMap::new();
    while let Some(a) = todo.pop() {
        let sy = cells[a.c as usize].0;
        let (w, right, ns) = match t[a.st as usize * NY + sy as usize] { None => return Err("abstract halt".into()), Some(x) => x };
        let code = (a.st as usize * NY + sy as usize) as u8;
        let mut carry = a.carry.clone();
        let tag: Vec<u8> = match mode {
            0 => vec![],
            1 => { let mut x = cells[a.c as usize].1.clone(); tag_push(0, h, &mut x, code); x }
            2 | 3 => { tag_push(mode, h, &mut carry, code); carry.clone() }
            _ => return Err("bad mode".into()),
        };
        let wc = intern((w, tag), &mut cells);
        let (pop, keep) = if right { (&a.r, &a.l) } else { (&a.l, &a.r) };
        let mut pushed = Vec::with_capacity(n); pushed.push(wc); pushed.extend_from_slice(&keep[..n - 1]);
        let prefix = pop[1..].to_vec();
        // record pushed gram, wake waiters on that side
        let (gs, ps, ws) = if right { (&mut gl, &mut pl, &mut wl) } else { (&mut gr, &mut pr, &mut wr) };
        if gs.insert(pushed.clone()) {
            let pf = pushed[..n - 1].to_vec(); let x = pushed[n - 1];
            ps.entry(pf.clone()).or_default().push(x);
            if let Some(list) = ws.get(&pf) { for b in list.clone() { todo.push(b); } }
        }
        // subscribe this config to its prefix, then expand with the current possibilities
        let (ps2, ws2) = if right { (&pr, &mut wr) } else { (&pl, &mut wl) };
        let list = ws2.entry(prefix.clone()).or_default(); if !list.contains(&a) { list.push(a.clone()); }
        if let Some(xs) = ps2.get(&prefix) {
            for &x in xs {
                let mut np = prefix.clone(); np.push(x);
                let nx = if right { Abs { st: ns, carry: carry.clone(), c: pop[0], l: pushed.clone(), r: np } } else { Abs { st: ns, carry: carry.clone(), c: pop[0], l: np, r: pushed.clone() } };
                if seen.insert(nx.clone()) { todo.push(nx); if seen.len() > 5_000_000 { return Err("too big".into()); } }
            }
        }
    }
    Ok(seen.len())
}

// Repeated word list. A word is a vector of cells; a token is (word, exponent), exponent == thr means "at least thr".
type Tok = (Vec<u8>, u32);
fn push_tok(st: &mut Vec<Tok>, w: Vec<u8>, tail: &[u8], thr: u32) {
    if st.is_empty() && w == tail { return; }
    if let Some(top) = st.last_mut() { if top.0 == w { top.1 = (top.1 + 1).min(thr); return; } }
    st.push((w, 1u32.min(thr)));
}
fn norm(st: &mut Vec<Tok>, tail: &[u8]) { while !st.is_empty() && st[0].0 == tail { st.remove(0); } }
fn walk(t: &Trans, w: &mut Vec<u8>, st: &mut u8, off: usize) -> Result<bool, String> { // true: exits right
    let mut p = off as i64; let n = w.len() as i64;
    for _ in 0..100000 {
        let (x, r, ns) = t[*st as usize * NY + w[p as usize] as usize].ok_or("abstract halt")?;
        w[p as usize] = x; *st = ns; p += if r { 1 } else { -1 };
        if p < 0 { return Ok(false); } if p >= n { return Ok(true); }
    }
    Err("block simulation too long".into())
}
fn check_repwl(spec: &Spec, t: &Trans, l: usize, thr: u32, k: usize, presim: u64) -> Result<usize, String> {
    if presim != 0 { return Err("presim unsupported".into()); }
    if l % spec.lp.len() != 0 || l % spec.rp.len() != 0 || k >= l { return Err("bad L".into()); }
    let block = |b: i64| -> Vec<u8> { (0..l as i64).map(|i| spec.at(b + i)).collect() };
    let b0 = -(k as i64); let (fl, fr) = (-(spec.left.len() as i64) - 1, spec.right.len() as i64 + 1);
    // right stack, built far to near; tail is the first block fully past the finite part
    let mut top = b0 + l as i64; while top <= fr - 1 { top += l as i64; } let tail_r = block(top);
    let mut rs: Vec<Tok> = vec![]; let mut b = top - l as i64;
    while b >= b0 + l as i64 { push_tok(&mut rs, block(b), &tail_r, thr); b -= l as i64; }
    // first block lying wholly left of the finite part of the tape
    let mut low = b0 - l as i64; while low + l as i64 - 1 >= fl + 1 { low -= l as i64; } let tail_l = block(low);
    let mut ls: Vec<Tok> = vec![]; let mut b = low + l as i64;
    while b <= b0 - l as i64 { push_tok(&mut ls, block(b), &tail_l, thr); b += l as i64; }
    norm(&mut ls, &tail_l); norm(&mut rs, &tail_r);
    let mut st = 0u8; let mut w = block(b0);
    let ex = walk(t, &mut w, &mut st, k)?;
    if ex { push_tok(&mut ls, w, &tail_l, thr); } else { push_tok(&mut rs, w, &tail_r, thr); }
    // config: (state, facing right?, left, right); head stands just outside the top of the opposite stack
    type C = (u8, bool, Vec<Tok>, Vec<Tok>);
    let s0: C = (st, ex, ls, rs);
    let mut seen: HashSet<C> = HashSet::new(); seen.insert(s0.clone()); let mut todo = vec![s0];
    while let Some((s, fr2, ls, rs)) = todo.pop() {
        let (pop_stack, tail) = if fr2 { (&rs, &tail_r) } else { (&ls, &tail_l) };
        let mut outs: Vec<(Vec<u8>, Vec<Tok>)> = vec![];
        match pop_stack.last() {
            None => outs.push((tail.clone(), vec![])),
            Some((w, e)) => {
                let mut a = pop_stack.clone(); a.pop(); let mut rest = a.clone();
                if *e > 1 { rest.push((w.clone(), *e - 1)); } norm(&mut rest, tail);
                outs.push((w.clone(), rest));
                if *e == thr { let mut same = a; same.push((w.clone(), thr)); norm(&mut same, tail); outs.push((w.clone(), same)); }
            }
        }
        for (mut w, rest) in outs {
            let mut st2 = s; let ex = walk(t, &mut w, &mut st2, if fr2 { 0 } else { l - 1 })?;
            let (mut nl, mut nr) = if fr2 { (ls.clone(), rest) } else { (rest, rs.clone()) };
            if ex { push_tok(&mut nl, w, &tail_l, thr); } else { push_tok(&mut nr, w, &tail_r, thr); }
            let c: C = (st2, ex, nl, nr);
            if seen.insert(c.clone()) { todo.push(c); if seen.len() > 5_000_000 { return Err("too big".into()); } }
        }
    }
    Ok(seen.len())
}

// Closed language over run-compressed blocks. Automaton state: last K runs of whole blocks (value, length mod M, 0 for the blank
// tail) plus the unfinished block. Each side's word follows only edges in that side's edge set; start phases per OFF.
#[derive(Clone, PartialEq, Eq, Hash)]
struct AS { runs: Vec<(u32, u32)>, part: u32, ph: u32, odd: bool, tail: bool }
fn as_step(q: &AS, a: u8, m: u32, b: u32, cmask: u32) -> AS {
    if q.tail && a == 0 { return q.clone(); } // anchored blank tail stays
    let odd = q.odd ^ (cmask >> a & 1 == 1);
    let part = q.part | ((a as u32) << (2 * q.ph));
    if q.ph + 1 < b { return AS { runs: q.runs.clone(), part, ph: q.ph + 1, odd, tail: false }; }
    let mut runs = q.runs.clone(); let last = *runs.last().unwrap();
    if last.0 == part && last.1 == 0 { }
    else if last.0 == part { let n = runs.len(); runs[n - 1].1 = last.1 % m + 1; }
    else { runs.remove(0); runs.push((part, 1)); }
    AS { runs, part: 0, ph: 0, odd, tail: false }
}
fn check_runlang(spec: &Spec, t: &Trans, k: usize, m: u32, b: u32, off: i64, cmask: u32) -> Result<usize, String> {
    if spec.lp != [0] || spec.rp != [0] { return Err("finite tapes only".into()); }
    let mut ids: HashMap<AS, u32> = HashMap::new(); let mut sts: Vec<AS> = vec![];
    fn id(q: AS, ids: &mut HashMap<AS, u32>, sts: &mut Vec<AS>) -> u32 { if let Some(&i) = ids.get(&q) { i } else { let i = sts.len() as u32; sts.push(q.clone()); ids.insert(q, i); i } }
    let tail = vec![(0u32, 0u32); k];
    // edge sets: target -> set of (source, letter); index 0 left, 1 right
    let mut into: [HashMap<u32, Vec<(u32, u8)>>; 2] = [HashMap::new(), HashMap::new()];
    let mut edges: [HashSet<(u32, u8)>; 2] = [HashSet::new(), HashSet::new()];
    let mut nxt: HashMap<(u32, u8), u32> = HashMap::new();
    macro_rules! next { ($q:expr, $a:expr) => {{ let qq: u32 = $q; let aa: u8 = $a; if let Some(&x) = nxt.get(&(qq, aa)) { x } else { let s2 = as_step(&sts[qq as usize], aa, m, b, cmask); let x = id(s2, &mut ids, &mut sts); nxt.insert((qq, aa), x); x } }} }
    macro_rules! add { ($side:expr, $q:expr, $a:expr) => {{ let sd: usize = $side; let qq: u32 = $q; let aa: u8 = $a; let tt = next!(qq, aa); if edges[sd].insert((qq, aa)) { into[sd].entry(tt).or_default().push((qq, aa)); true } else { false } }} }
    let anchored = off < 0;
    let phases = if anchored { 1 } else { b };
    for p in 0..phases { let q = id(AS { runs: tail.clone(), part: 0, ph: p, odd: false, tail: anchored }, &mut ids, &mut sts); add!(0, q, 0); add!(1, q, 0); }
    let nl = spec.left.len() as i64; let nr = spec.right.len() as i64; let bb = b as i64;
    let ph_l = if anchored { 0 } else { (-nl - off).rem_euclid(bb) as u32 };
    let ph_r = if anchored { 0 } else { (off + bb - 1 - nr).rem_euclid(bb) as u32 };
    let mut ql = id(AS { runs: tail.clone(), part: 0, ph: ph_l, odd: false, tail: anchored }, &mut ids, &mut sts);
    for &a in &spec.left { add!(0, ql, a); ql = next!(ql, a); }
    let mut qr = id(AS { runs: tail.clone(), part: 0, ph: ph_r, odd: false, tail: anchored }, &mut ids, &mut sts);
    for &a in spec.right.iter().rev() { add!(1, qr, a); qr = next!(qr, a); }
    let start = (ql, 0u8, spec.head, qr);
    let mut seen: HashSet<(u32, u8, u8, u32)> = HashSet::new(); seen.insert(start); let mut list = vec![start];
    loop {
        let mut changed = false; let mut i = 0;
        while i < list.len() {
            let (l, s, c, r) = list[i]; i += 1;
            let (w, right, ns) = t[s as usize * NY + c as usize].ok_or("abstract halt")?;
            let (side, pq, oq) = if right { (0usize, l, r) } else { (1usize, r, l) };
            if add!(side, pq, w) { changed = true; }
            let np = next!(pq, w);
            let inc: Vec<(u32, u8)> = into[1 - side].get(&oq).cloned().unwrap_or_default();
            for (from, y) in inc {
                let nx = if right { (np, ns, y, from) } else { (from, ns, y, np) };
                if seen.insert(nx) { list.push(nx); changed = true; if seen.len() > 20_000_000 { return Err("too big".into()); } }
            }
        }
        if !changed { break; }
    }
    Ok(seen.len())
}

#[derive(Clone)]
enum Rec { H(u64), C(u64, u64, i64), P(usize, u32, usize, u64), W(usize, u32, usize, u64), L(usize, u32, u32, i64, u32), X(String) }

fn verify_external(tm: &str, what: &str, externals: &HashSet<String>) -> Result<(), String> {
    if externals.contains(&format!("{} {}", tm, what)) { Ok(()) } else { Err("no externally verified certificate".into()) }
}

fn children(t: &Trans, sym_mask: u32, slot: usize, spec_syms: u32) -> Vec<Trans> {
    // new-state rule: a state above the highest used may only be the next one (here at most B).
    let _ = spec_syms;
    let mut maxs = 0u8; for x in t.iter().flatten() { maxs = maxs.max(x.2); }
    let smax = (maxs + 1).min(NS as u8 - 1);
    let fresh = (1..NY as u8).find(|y| sym_mask >> y & 1 == 0);
    let mut out = vec![];
    for w in 0..NY as u8 {
        if sym_mask >> w & 1 == 0 && Some(w) != fresh { continue; }
        for r in [false, true] { for n in 0..=smax { let mut c = *t; c[slot] = Some((w, r, n)); out.push(c); } }
    }
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() >= 4 && args[1] == "--one" { // check --one TAPE W|P|L TM params...: verify a single non-halting certificate
        let spec = parse_tape(&args[2]); let t = parse_tm(&args[4]); let n = |i: usize| args[5 + i].parse::<i64>().unwrap();
        let res = match args[3].as_str() {
            "P" => check_cps(&spec, &t, n(0) as usize, n(1) as u32, n(2) as usize, n(3) as u64),
            "W" => check_repwl(&spec, &t, n(0) as usize, n(1) as u32, n(2) as usize, n(3) as u64),
            "L" => check_runlang(&spec, &t, n(0) as usize, n(1) as u32, n(2) as u32, n(3), n(4) as u32),
            _ => Err("unknown record".into()),
        };
        println!("{} {:?}", args[4], res); std::process::exit(if res.is_ok() { 0 } else { 1 });
    }
    if args.len() < 4 { eprintln!("usage: check TAPE THRESHOLD LEDGER... | check --one TAPE W|P|L TM params..."); std::process::exit(2); }
    let spec = parse_tape(&args[1]); let threshold: u64 = args[2].parse().unwrap();
    let mut recs: HashMap<u64, Rec> = HashMap::new(); let mut externals: HashSet<String> = HashSet::new();
    let mut i = 3;
    while i < args.len() {
        if args[i] == "--external" { let f = std::fs::File::open(&args[i + 1]).unwrap(); for l in BufReader::new(f).lines() { externals.insert(l.unwrap()); } i += 2; continue; }
        let f = std::fs::File::open(&args[i]).unwrap_or_else(|e| panic!("{}: {}", args[i], e));
        for line in BufReader::with_capacity(1 << 20, f).lines() {
            let line = line.unwrap(); let p: Vec<&str> = line.split_whitespace().collect();
            if p.is_empty() { continue; }
            let (tm, r) = match p[0] {
                "H" => (p[2], Rec::H(p[1].parse().unwrap())),
                "C" => (p[4], Rec::C(p[1].parse().unwrap(), p[2].parse().unwrap(), p[3].parse().unwrap())),
                "P" => (p[1], Rec::P(p[2].parse().unwrap(), p[3].parse().unwrap(), p[4].parse().unwrap(), p[5].parse().unwrap())),
                "W" => (p[1], Rec::W(p[2].parse().unwrap(), p[3].parse().unwrap(), p[4].parse().unwrap(), p[5].parse().unwrap())),
                "L" => (p[1], Rec::L(p[2].parse().unwrap(), p[3].parse().unwrap(), p[4].parse().unwrap(), p[5].parse().unwrap(), p[6].parse().unwrap())),
                "X" => (p[1], Rec::X(p[2..].join(" "))),
                _ => panic!("bad line {}", line),
            };
            if recs.insert(key(&parse_tm(tm)), r).is_some() { panic!("duplicate record for {}", tm); }
        }
        i += 1;
    }
    let total = recs.len();
    let root_syms = spec.symbols();
    let mut stack: Vec<(Trans, u32)> = vec![([None; NS * NY], root_syms)];
    let sanity: u64 = std::env::var("CHECK_SANITY").ok().and_then(|x| x.parse().ok()).unwrap_or(20000);
    let threads: usize = std::env::var("CHECK_THREADS").ok().and_then(|x| x.parse().ok()).unwrap_or(2);
    // Serial walk of the top of the tree, parallel below.
    let (mut nh, mut nc, mut np, mut nw, mut nl, mut nx) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64); let mut used = 0u64; let mut errors = 0u64;
    let mut tops: Vec<(u64, String)> = vec![];
    let recs = std::sync::Arc::new(recs); let spec = std::sync::Arc::new(spec); let externals = std::sync::Arc::new(externals);
    let mut level: Vec<(Trans, u32)> = vec![]; std::mem::swap(&mut level, &mut stack);
    while !level.is_empty() {
        let chunk = level.len() / threads + 1; let mut handles = vec![];
        let parts: Vec<Vec<(Trans, u32)>> = level.chunks(chunk).map(|c| c.to_vec()).collect(); level = vec![];
        for part in parts {
            let (recs, spec, externals) = (recs.clone(), spec.clone(), externals.clone());
            handles.push(std::thread::spawn(move || {
                let mut next = vec![]; let (mut nh, mut nc, mut np, mut nw, mut nl, mut nx, mut used, mut errors) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64); let mut tops: Vec<(u64, String)> = vec![];
                for (t, syms) in part {
                    let name = tm_to_string(&t);
                    let rec = match recs.get(&key(&t)) { Some(r) => r.clone(), None => { eprintln!("MISSING {}", name); errors += 1; continue; } };
                    used += 1;
                    if !matches!(rec, Rec::H(_)) {
                        let mut r = Run::new(&spec); let mut halted = false;
                        for _ in 0..sanity { if !r.step(&t) { halted = true; break; } }
                        if halted { eprintln!("FAILED {} : non-halting record but it halts at step {}", name, r.steps + 1); errors += 1; }
                    }
                    let res: Result<(), String> = match rec {
                        Rec::H(steps) => {
                            let mut r = Run::new(&spec); let mut ok = Ok(());
                            while r.steps + 1 < steps { if !r.step(&t) { ok = Err(format!("halts early at {}", r.steps + 1)); break; } }
                            if ok.is_ok() {
                                let slot = r.st as usize * NY + r.cur as usize;
                                if t[slot].is_some() { ok = Err("not undefined at the claimed step".into()); }
                                else {
                                    nh += 1; if steps >= threshold { eprintln!("AT OR ABOVE THRESHOLD {} {}", steps, name); errors += 1; }
                                    if steps > 1000 { tops.push((steps, name.clone())); }
                                    let filled = t.iter().filter(|x| x.is_some()).count();
                                    if filled < NS * NY - 1 {
                                        for c in children(&t, syms, slot, 0) { let w = c[slot].unwrap().0; next.push((c, syms | 1 << w)); }
                                    }
                                }
                            }
                            ok
                        }
                        Rec::C(a, b, d) => { nc += 1; check_lin(&spec, &t, a, b, d) }
                        Rec::P(n, m, h, q) => { np += 1; check_cps(&spec, &t, n, m, h, q).map(|_| ()) }
                        Rec::W(l, th, k, q) => { nw += 1; check_repwl(&spec, &t, l, th, k, q).map(|_| ()) }
                        Rec::L(k, m, b, o, c) => { nl += 1; check_runlang(&spec, &t, k, m, b, o, c).map(|_| ()) }
                        Rec::X(what) => { nx += 1; if what == "holdout" { Ok(()) } else { verify_external(&name, &what, &externals) } }
                    };
                    if let Err(e) = res { eprintln!("FAILED {} : {}", name, e); errors += 1; }
                }
                (next, nh, nc, np, nw, nl, nx, used, errors, tops)
            }));
        }
        for h in handles { let (n, a, b, c, d, f, e, u, er, tp) = h.join().unwrap(); level.extend(n); nh += a; nc += b; np += c; nw += d; nl += f; nx += e; used += u; errors += er; tops.extend(tp); }
    }
    tops.sort(); tops.reverse();
    println!("tape {} threshold {}", args[1], threshold);
    println!("nodes visited {} ledger records {} errors {}", used, total, errors);
    println!("halting {} lin {} cps {} repwl {} runlang {} holdouts-declared {}", nh, nc, np, nw, nl, nx);
    println!("top halters:"); for (s, m) in tops.iter().take(12) { println!("  {} {}", s, m); }
    if used as usize != total { println!("UNUSED LEDGER RECORDS: {}", total as i64 - used as i64); }
    if errors != 0 || used as usize != total { println!("VERDICT: FAIL"); std::process::exit(1); }
    if nx != 0 { println!("VERDICT: PARTIAL: every machine outside the {} declared holdouts halts in fewer than {} steps or never halts", nx, threshold); return; }
    println!("VERDICT: PASS: every machine on this tape halts in fewer than {} steps or never halts", threshold);
}
