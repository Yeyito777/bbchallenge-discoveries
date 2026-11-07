# `1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE` halts from the blank tape

**Status (2026-11-07): closed Rocq theorem.** `c273_halts : halts tm c0` in `kernel/final/Halts273.v` is checked by the Rocq kernel. Its assumptions are only Rocq's primitive 63-bit integers and their specifications (the same base as `rocq/bb6`). The orbit is checked inside the kernel with `native_cast_no_check`, in 523 jobs. The exact raw step count comes from two independent counters that agree.

## Claim

Write A(a,b,c) = `0^inf 1^a (10)^b C> 1^c 0^inf`. The machine reaches A(0,1,0) after 2 steps from blank. Iterating the rule map from A(0,1,0), the orbit reaches

| Quantity | Exact value |
|---|---|
| Halting state | A(80724428909535, 1, 242173286728609), so c = 3a+4 |
| Map steps from A(0,1,0) to that state | 71755048174256 |
| Ones on the final tape | 161448857819077 (= 2a+b+6) |
| Raw steps from blank to the halting configuration | 831265665802914901834939426973647910800303 (about 8.31e41) |
| Counting the halting transition | 831265665802914901834939426973647910800304 |

From A(a,b,3a+4) the machine halts: a drains to A(0,2a+b,4), then it reaches state A reading 1, which has no transition.

## The map

From the wiki page (analysis by Shawn Ligocki), with k = floor(c/3), r = c mod 3:

```
c <  3a+3 :  A(a,b,c) -> A(4k+2b+2r+1, 1, a-k+1)
c =  3a+3 or 3a+4 :  halt
c >= 3a+5 :  A(a,b,c) -> A(4a+2b+4, 2, c-3a-5)
```

One correction to the wiki's low-level rule A(a,b,0) -> A(2b+1,1,a+1): it fails for b=1, a>=1. That family is unreachable (b=1 only ever comes with c>=1, and the start A(0,1,0) is fine), so the map above is unaffected. The Rocq proof carries this as an invariant.

## Raw step count

Per rule, from the step counts in `rocq/Rules273.v` (each low-level lemma has an exact count; these sum them):

- drain(k,b) = sum over i<k of (4(b+2i)+9) = k(4b+4k+5)
- c < 3a+3, with a0=a-k, B=b+2k: drain(k,b) + a0(4B+c1[r]) + 6B + c0[r], with c1 = (1,5,9), c0 = (6,14,24)
- c >= 3a+5: drain(a,b) + 12a + 6b + 25
- the first rule, A(0,1,0) -> A(3,1,1): 12 steps
- halting stretch from A(a,b,3a+4): drain(a,b) + 8(2a+b) + 33 steps to the configuration with no transition

Total = 2 + 12 + the per-rule sum over the orbit, plus the halting stretch. The halting transition itself is not counted (busycoq's `halts_in` convention); add 1 to count it.

Checks of the formula against the raw TM:

- every one of the first 6,998 rules from blank matches the raw step at which the next map state appears (778271620087 at rule 6,998)
- the halting stretch matches in 80 cases (a < 40, b in {1,2}), and so does the ones formula

The total was computed by two counters, `count273.c` and `count273.rs` (written separately, from the same formulas), over all 523 jobs on a 128-core box. Every job's end state matched the next checkpoint, and the two counters gave the same value on every job (`kernel/final/sum.out`: 0 differences). Total: **831265665802914901834939426973647910800303** steps from blank to the configuration with no transition, or 831265665802914901834939426973647910800304 counting the halting transition. The counts are not proved in Rocq: the per-rule formula rests on the lemma counts plus the raw-TM checks above.

## How it was found and checked

- **Main run** (`code/hunt.c`, `code/maps.h`, C, about 611M map steps/s): checkpoints every 2^37 map steps. The halt was hit at 19:42Z on 2026-11-06, after about 33 hours of run time.
- **Second implementation** (`code/verify/verify.rs`, Rust, from the wiki's rules). It replayed every one of the 522 checkpoint intervals and compared end state, a hash of the state every 2^16 steps, and the count of states with |c-3a-3| <= 8192: 522 of 522 equal. From the last checkpoint (n = 71743133712384) it halts at the same map step in the same state (`box/c273/HALT.second`).
- **Rule map from the raw machine:** `rocq/Rules273.v` proves `halts_of_orbit : iter N (0,1,0) = None -> halts tm c0` for `step273`, the map above, with exact low-level step counts. `Print Assumptions`: closed under the global context.
- **Raw TM:** an hour from blank matched all of the first 7,000 map states exactly (`validation/raw_c273.out`). A rule grid from S=0 to 1200 checked every branch, including both halts (`validation/grid_c273.out`). A raw replay of the final stretch is out of reach: one rule there costs about S^2 = 1e29 raw steps.

## Kernel proof (done 2026-11-07)

`kernel/Kernel273.v` defines the map on Rocq's primitive 63-bit integers (`step63`, iterated by binary recursion in `itp`). It proves that `itp p` agrees with p steps of `step273` while a+2b+c+6p < 2^61 (a+2b+c grows by at most 6 per step). Then `chain` composes jobs. `kernel/Final273.v` proves `halts_of_chain : chain 0 1 0 -> halts tm c0`; its assumptions are only the primitive integer operations and their specifications, the same base as `rocq/bb6`.

`kernel/gen_jobs.py` writes 523 jobs: 522 of the form "from checkpoint i, 2^37 steps reach checkpoint i+1", plus "from the last checkpoint, 11914461873 steps reach Halt". Each is checked by `native_cast_no_check` at `Qed`. `Chain.v` builds `chain 0 1 0` from them and states `c273_halts : halts tm c0`. Measured on the hunt box (EPYC 9R14):
- J0000 (from A(0,1,0)) and J0521: 1,726 s each, 446 MB maximum RSS.
- J0522 (the halting stretch): 143 s.
- `TestChain.v` composes J0521 and J0522 into `chain` at checkpoint 521. Its assumptions are only the primitive int operations.
- All 523 jobs: about 250 core-hours.

**Result.** All 523 kernel jobs passed on a 128-core spot box (m7a.32xlarge, 2026-11-06 21:26Z to 2026-11-07 03:27Z) with no failures. `Chain.v` composes them into `c273_chain : chain i0 i1 i0`. `Halts273.v` applies `halts_of_chain`. `Check c273_halts : halts tm c0`. `Print Assumptions c273_halts` lists only `PrimInt63.{int,add,sub,mul,div,ltb,eqb,land,lsr}` and `Uint63.{add,sub,mul,div,ltb}_spec` (`kernel/final/Halts273.log`). The final statement sits in its own file because BusyCoq's `>>` notation clashes with Uint63's when both are imported in one file. `gen_jobs.py` now writes `Chain.v` and `Halts273.v` separately.

## Reproduce

```sh
# runs and checks (code/, gcc 14 and rustc)
cd code
gcc-14 -O2 -march=native -w -DM_c273 -o hunt_c273 hunt.c -lm && ./hunt_c273 RUN 50   # main run, resumable
rustc --edition 2021 -C opt-level=3 -C target-cpu=native -o verify verify/verify.rs
./verify c273 RUN 2 once                              # second implementation over every interval
./verify c273 RUN 0 halt                              # second implementation from the last checkpoint to the halt
cd ..
# rule map in Rocq (Rocq 8.20.1, busycoq from rocq/bb6/busycoq)
coqc -Q busycoq BusyCoq rocq/Rules273.v
# kernel proof and raw-step counts, resumable (see kernel/run_all.sh)
cd kernel && ./run_all.sh setup && ./run_all.sh jobs 120 && ./run_all.sh chain && python3 sum_counts.py .   # from kernel/; chain compiles Chain.v then Halts273.v
```

## Credit

The rules, the probabilistic model and the 2T-rule-step simulation are Shawn Ligocki's, on the wiki page https://wiki.bbchallenge.org/wiki/1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE (last edited 2026-05-01).
