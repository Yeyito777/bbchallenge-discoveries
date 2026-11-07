// Second, independent raw-step count for c273: written from the Rocq lemma counts directly (drain loop summed in closed form,
// tail rules case by case as in R_c0, R_c1, R_c2_step, R_c2_zero, R_reset, R_halt4), with u128 limbs and its own carry.
// usage: count273r a b c N [halt]   same output as count273.c
fn main() {
    let v: Vec<String> = std::env::args().collect();
    let (mut a, mut b, mut c): (u128, u128, u128) = (v[1].parse().unwrap(), v[2].parse().unwrap(), v[3].parse().unwrap());
    let n: u64 = v[4].parse().unwrap();
    let halt = v.len() > 5 && v[5] == "halt";
    let (mut lo, mut hi): (u128, u128) = (0, 0);
    let mut add = |x: u128| { let (s, o) = lo.overflowing_add(x); lo = s; if o { hi += 1; } };
    // sum over i<k of (4(b+2i)+9)
    let drain = |k: u128, b: u128| -> u128 { k * (4 * b + 9) + 4 * k * k - 4 * k }; // sum of 4(b+2i)+9 over i<k
    for _ in 0..n {
        if c < 3 * a + 3 {
            let c64 = c as u64;
            let (k, r) = ((c64 / 3) as u128, (c64 % 3) as u128);
            let a0 = a - k;
            let bb = b + 2 * k; // (10)^bb after draining
            let tail = match r {
                0 => { assert!(bb >= 2); let b0 = bb - 2; a0 * (4 * b0 + 9) + (6 * b0 + 18) }               // R_c0 a0 b0
                1 => { let b0 = bb - 1; 2 + a0 * (4 * b0 + 9) + (6 * b0 + 18) }                            // R_c1 a0 b0
                _ => { let b0 = bb - 1; if a0 == 0 { 6 * b0 + 30 } else { (4 * b0 + 19) + (a0 - 1) * (4 * (b0 + 1) + 9) + (6 * (b0 + 1) + 18) } }
            };
            add(drain(k, b) + tail);
            let na = 4 * k + 2 * b + 2 * r + 1; c = a - k + 1; a = na; b = 1;
        } else {
            assert!(c >= 3 * a + 5, "halting state reached early");
            add(drain(a, b) + 6 * (2 * a + b) + 25);                                                      // drains, then R_reset
            let na = 4 * a + 2 * b + 4; c -= 3 * a + 5; a = na; b = 2;
        }
    }
    if halt {
        assert!(c == 3 * a + 4);
        let bb = 2 * a + b;
        add(drain(a, b) + 5 + 2 * bb + 3 + 4 * (bb + 2) + 8 + 2 * (bb + 4) + 1);                          // R_halt4's steps
    }
    // decimal of hi*2^128+lo
    let mut w = [lo as u64, (lo >> 64) as u64, hi as u64, (hi >> 64) as u64];
    let mut d = Vec::new();
    loop {
        let mut r: u128 = 0;
        for i in (0..4).rev() { let cur = (r << 64) | w[i] as u128; w[i] = (cur / 10) as u64; r = cur % 10; }
        d.push((b'0' + r as u8) as char);
        if w.iter().all(|&x| x == 0) { break; }
    }
    let s: String = d.into_iter().rev().collect();
    println!("{} {} {} {}", a, b, c, s);
}
