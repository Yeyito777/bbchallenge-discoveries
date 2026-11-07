# `1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE` halts

**Independent rebuild: in progress.** The proof passed on its original run (all 523 jobs, final theorem checked). A second, from-scratch rebuild on a separate machine is running; this line will be updated when it finishes.

This BB(6) holdout, the "skewed tent map" machine on the wiki, halts from the blank tape. It is the only machine in its equivalence class. The halt is a closed Rocq theorem, proved in the kernel:

```coq
Theorem c273_halts : halts tm c0.
```

with `tm` the machine and `c0` the blank tape, as defined in busycoq. It is in [`kernel/Halts273.v`](kernel/Halts273.v). `Print Assumptions c273_halts` lists only Rocq's primitive 63-bit integers and the specifications of the ones used: `PrimInt63.{int,add,sub,mul,div,ltb,eqb,land,lsr}` and `Uint63.{add,sub,mul,div,ltb}_spec` ([`kernel/final/Halts273.log`](kernel/final/Halts273.log)).

| Quantity | Value |
|---|---|
| Configuration | A(a,b,c) = `0^inf 1^a (10)^b C> 1^c 0^inf`; the blank tape reaches A(0,1,0) in 2 steps |
| Halting state | A(80724428909535, 1, 242173286728609), where c = 3a+4 |
| Map steps from A(0,1,0) | 71,755,048,174,256 |
| Raw steps from blank, without the halting transition | 831265665802914901834939426973647910800303 (about 8.31×10^41) |
| Counting the halting transition | 831265665802914901834939426973647910800304 |
| Ones on the final tape | 161448857819077 |

The step count is not a Rocq theorem. It comes from a per-rule formula built from the exact step counts of the proved rule lemmas. The formula was checked against the raw machine on its first 6,998 rules and on 80 halting stretches. Two separately written counters, in C and Rust, agree on every one of the 523 jobs (`kernel/final/sum.out`).

## How it is proved

- `rocq/Rules273.v` (= `kernel/Rules273.v`) proves the rule map from the raw machine, every branch, with exact low-level step counts: `halts_of_orbit : iter N (0,1,0) = None -> halts tm c0`. It has no assumptions.
- `kernel/Kernel273.v` runs the map on primitive 63-bit integers and proves it agrees with the map while the numbers stay below 2^61. `kernel/Final273.v` turns a chain of jobs into `halts tm c0`.
- `kernel/jobs/` holds 523 jobs, one per checkpoint interval of 2^37 map steps plus the halting stretch, each checked in the kernel with `native_compute`. `kernel/Chain.v` composes them.
- Cost: 280 core-hours in total, about 1,930 s and under 450 MB per job, on a 128-core AWS machine (`kernel/final/times.txt`). On an 8-core desktop that is about 35 hours and 4 GB (scaled, not measured). Like Coq-BB5's proofs, this trusts `ocamlopt` through `native_compute`.

## Build

Rocq 8.20.1 with native compilation (opam switch `rocq`), gcc and rustc:

```sh
cd kernel
./run_all.sh setup          # BusyCoq, Rules273, Kernel273, Final273 and both counters: a few minutes
./run_all.sh jobs 8         # 523 kernel jobs and 1,046 counts, restartable
./run_all.sh chain          # Chain.v, then Halts273.v with Print Assumptions
python3 sum_counts.py .     # the exact raw-step total
```

See `kernel/RUN.md`. The full write-up, with the map and the other checks (a second implementation in Rust over every interval, raw-machine checks), is [`HALT.md`](HALT.md).

## Files

- `HALT.md`: the result and every check.
- `code/`: the run (`hunt.c`, `maps.h`), the second implementation (`verify/verify.rs`), raw-machine checks (`rawcheck.c`, `rawgrid.c`, `rawhalt.py`) and step counting (`count273.c`, `count273.rs`, `stepcount273.c`, `steps273.py`). Build with `gcc -O2 -march=native -w -DM_c273`, see `HALT.md`.
- `rocq/`, `kernel/`: the Rocq proof. `kernel/busycoq/` is a subset of busycoq (MIT, licence files kept).
- `box/c273/`: the run's checkpoints, the halt, and the second implementation's results. `validation/`: the raw-machine checks.
- The kernel jobs' logs, the per-job counts and the near-miss log are in the `evidence-logs-v3` asset of the v3 release.

## Credits

Shawn Ligocki found the rules, wrote the probabilistic model, simulated 2T rule steps and wrote the [wiki page](https://wiki.bbchallenge.org/wiki/1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE). busycoq is by Maja Kądziołka, via ccz181078's BB6 branch.

## Licence

MIT: [`LICENSE`](LICENSE), Copyright (c) 2026 Yeyito (https://github.com/Yeyito777). `kernel/busycoq/` keeps busycoq's MIT notices.
