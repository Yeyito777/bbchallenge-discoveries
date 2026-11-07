// Second, independent implementation. Reads a run's ckpt.log, replays every checkpoint interval from its start state with
// its own form of the map, and compares end state, block hash and window count. Thread-parallel across intervals.
// usage: verify c273 DIR THREADS [once]  (this copy has only the c273 map)
// Writes DIR/verified.log (one line per interval: start_n end_n OK) and DIR/MISMATCH on any difference.
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::sync::{Arc, Mutex};
use std::collections::BTreeSet;

const W: i64 = 8192;
const BLOCK: u64 = 1 << 16;
const K: u64 = 0x9E3779B97F4A7C15;
#[inline(always)] fn mix1(h: u64, v: u64) -> u64 { (h ^ v).rotate_left(23).wrapping_mul(K) }

#[derive(Clone, Debug, PartialEq)]
struct Ck { n: u64, v: [u64; 3], hash: u64, cnt: u64 }

fn parse_line(l: &str) -> Option<Ck> {
    let f: Vec<&str> = l.split_whitespace().collect();
    if f.len() < 9 { return None; }
    Some(Ck { n: f[0].parse().ok()?, v: [f[1].parse().ok()?, f[2].parse().ok()?, f[3].parse().ok()?],
              hash: u64::from_str_radix(f[4], 16).ok()?, cnt: f[5].parse().ok()? })
}

// Result of one interval: end state in canonical coordinates, or the map step at which it halted.
struct Out { v: [u64; 3], hash: u64, cnt: u64, halted: Option<u64> }

// c273 from the wiki's high-level rules.
fn run_c273(start: [u64; 3], steps: u64) -> Out {
    let (mut a, mut b, mut c) = (start[0] as i64, start[1] as i64, start[2] as i64);
    let (mut h, mut cnt) = (0u64, 0u64);
    let mut done = 0u64;
    while done < steps {
        for i in 0..BLOCK {
            let e = c - 3 * a - 3;
            cnt += ((e + W) as u64 <= (2 * W) as u64) as u64;
            if (e as u64) < 2 { return Out { v: [a as u64, b as u64, c as u64], hash: h, cnt, halted: Some(done + i) }; }
            let m = e >> 63; // all ones if a >= floor(c/3)
            let q = c / 3;
            let rem = c - 3 * q;
            let a1 = 4 * q + 2 * b + 2 * rem + 1;
            let c1 = a - q + 1;
            let a2 = 4 * a + 2 * b + 4;
            let c2 = e - 2;
            a = (a1 & m) | (a2 & !m);
            c = (c1 & m) | (c2 & !m);
            b = 2 + m; // m=-1 gives 1, m=0 gives 2
        }
        done += BLOCK;
        h = mix1(mix1(mix1(h, a as u64), b as u64), c as u64);
    }
    Out { v: [a as u64, b as u64, c as u64], hash: h, cnt, halted: None }
}

fn check_map(machine: &str, a: &Ck, b: &Ck) -> Result<(), String> {
    let steps = b.n - a.n;
    assert_eq!(machine, "c273");
    let o = run_c273(a.v, steps);
    if let Some(at) = o.halted { return Err(format!("HALT in verifier at {} state {:?}", a.n + at, o.v)); }
    if o.v == b.v && o.hash == b.hash && o.cnt == b.cnt { Ok(()) }
    else { Err(format!("interval {}..{}: verifier {:?} hash={:016x} cnt={} main {:?} hash={:016x} cnt={}", a.n, b.n, o.v, o.hash, o.cnt, b.v, b.hash, b.cnt)) }
}

fn verified_set(dir: &str) -> BTreeSet<u64> {
    let mut s = BTreeSet::new();
    if let Ok(t) = fs::read_to_string(format!("{}/verified.log", dir)) {
        for l in t.lines() { let f: Vec<&str> = l.split_whitespace().collect(); if f.len() >= 3 && (f[2] == "OK" || (f[2] == "NODUMP" && !std::path::Path::new(&format!("{}/dump/{}.bin", dir, f[0])).exists())) { if let Ok(x) = f[0].parse() { s.insert(x); } } }
    }
    s
}
fn complete_lines(t: &str) -> Vec<&str> { let mut v: Vec<&str> = t.split('\n').collect(); v.pop(); v }

// verify MACHINE DIR 0 halt: from the last checkpoint run until the map halts and print where, for comparison with DIR/HALT.
fn halt_mode(machine: &str, dir: &str) {
    let txt = fs::read_to_string(format!("{}/ckpt.log", dir)).unwrap();
    let lines = complete_lines(&txt);
    let last = lines[lines.len() - 1];
    assert_eq!(machine, "c273");
    let a = parse_line(last).unwrap();
    let o = run_c273(a.v, u64::MAX);
    println!("second implementation: halted, map_steps_done {} state {} {} {}", a.n + o.halted.unwrap(), o.v[0], o.v[1], o.v[2]);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let machine = args[1].clone(); let dir = args[2].clone(); let threads: usize = args[3].parse().unwrap();
    if args.len() > 4 && args[4] == "halt" { halt_mode(&machine, &dir); return; }
    let once = args.len() > 4;
    let vlog = Arc::new(Mutex::new(OpenOptions::new().create(true).append(true).open(format!("{}/verified.log", dir)).unwrap()));
    let taken = Arc::new(Mutex::new(verified_set(&dir)));
    let mut hs = Vec::new();
    for _ in 0..threads {
        let (machine, dir, vlog, taken) = (machine.clone(), dir.clone(), vlog.clone(), taken.clone());
        hs.push(std::thread::spawn(move || loop {
            let txt = fs::read_to_string(format!("{}/ckpt.log", dir)).unwrap_or_default();
            let lines = complete_lines(&txt);
            let mut job = None;
            {
                let mut t = taken.lock().unwrap();
                for i in 0..lines.len().saturating_sub(1) {
                    let n: u64 = lines[i].split_whitespace().next().unwrap().parse().unwrap();
                    if !t.contains(&n) { t.insert(n); job = Some(i); break; }
                }
            }
            match job {
                None => { if once { return; } std::thread::sleep(std::time::Duration::from_secs(30)); }
                Some(i) => {
                    let start = std::time::Instant::now();
                    let a = parse_line(lines[i]).unwrap(); let b = parse_line(lines[i + 1]).unwrap();
                    let (res, n0, n1) = (check_map(&machine, &a, &b), a.n, b.n);
                    let mut f = vlog.lock().unwrap();
                    // A missing list dump (lost with a reclaimed box) is not a mismatch: record it so a dump regeneration can fill it.
                    let res = match res { Err(e) if e.starts_with("no dump") => { writeln!(f, "{} {} NODUMP", n0, n1).unwrap(); f.sync_all().ok(); continue; } r => r };
                    match res {
                        Ok(()) => { writeln!(f, "{} {} OK {:.1}", n0, n1, start.elapsed().as_secs_f64()).unwrap(); }
                        Err(e) => {
                            writeln!(f, "{} {} MISMATCH {}", n0, n1, e).unwrap();
                            let mut m = OpenOptions::new().create(true).append(true).open(format!("{}/MISMATCH", dir)).unwrap();
                            writeln!(m, "{} {} {}", n0, n1, e).unwrap();
                        }
                    }
                    f.sync_all().ok();
                }
            }
        }));
    }
    for h in hs { h.join().unwrap(); }
}
