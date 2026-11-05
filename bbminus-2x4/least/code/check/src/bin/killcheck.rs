// killcheck: independent simulator for halting claims. Each input line: TAPE TM STEPS. Prints each line's verified step count
// and fails unless the machine reaches an undefined transition exactly on step STEPS. Two stacks, no shared code with the C tools.
use std::io::BufRead;
fn at(lp: &[u8], left: &[u8], head: u8, right: &[u8], rp: &[u8], pos: i64) -> u8 {
    if pos == 0 { return head; }
    if pos < 0 { let k = (-pos) as usize; if k <= left.len() { left[left.len() - k] } else { let j = k - left.len() - 1; lp[lp.len() - 1 - j % lp.len()] } }
    else { let k = pos as usize; if k <= right.len() { right[k - 1] } else { rp[(k - right.len() - 1) % rp.len()] } }
}
fn main() {
    let mut bad = 0; let mut n = 0;
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap(); let f: Vec<&str> = line.split_whitespace().collect(); if f.len() < 3 { continue; }
        let mut s = f[0]; let (mut lp, mut rp) = (vec![0u8], vec![0u8]);
        if s.starts_with('(') { let e = s.find(')').unwrap(); lp = s[1..e].bytes().map(|c| c - 48).collect(); s = &s[e + 1..]; }
        if s.ends_with(')') { let o = s.rfind('(').unwrap(); rp = s[o + 1..s.len() - 1].bytes().map(|c| c - 48).collect(); s = &s[..o]; }
        let o = s.find('[').unwrap(); let e = s.find(']').unwrap();
        let left: Vec<u8> = s[..o].bytes().map(|c| c - 48).collect(); let head = s.as_bytes()[o + 1] - 48; let right: Vec<u8> = s[e + 1..].bytes().map(|c| c - 48).collect();
        let tm = f[1].as_bytes(); let mut t = [None; 8];
        for i in 0..8 { let p = i * 3 + i / 4; if tm[p] != b'-' { t[i] = Some((tm[p] - 48, tm[p + 1] == b'R', (tm[p + 2] - 65) as usize)); } }
        let claim: u64 = f[2].parse().unwrap();
        let (mut ls, mut rs): (Vec<u8>, Vec<u8>) = (vec![], vec![]); let (mut cur, mut pos, mut st, mut steps) = (head, 0i64, 0usize, 0u64);
        let got = loop {
            let tr = t[st * 4 + cur as usize];
            match tr { None => break steps + 1, Some((w, r, ns)) => {
                if r { ls.push(w); pos += 1; cur = rs.pop().unwrap_or_else(|| at(&lp, &left, head, &right, &rp, pos)); }
                else { rs.push(w); pos -= 1; cur = ls.pop().unwrap_or_else(|| at(&lp, &left, head, &right, &rp, pos)); }
                st = ns; steps += 1; if steps > claim + 1 { break 0; }
            } }
        };
        n += 1; if got != claim { println!("MISMATCH {} got {}", line, got); bad += 1; } else { println!("OK {}", line); }
    }
    eprintln!("{} checked, {} mismatches", n, bad); if bad != 0 { std::process::exit(1); }
}
