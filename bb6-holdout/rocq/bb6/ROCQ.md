# BB(6) holdout `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`: Rocq

> Update 2026-11-05: `halts tm c0` is now a closed theorem, proved in the kernel by a different checker in `../bb6-fast/`. This folder's checker and its extracted run remain the evidence for the exact step count, so "no closed Rocq theorem" below now refers to the step count only.

**Status: there is no fast Rocq proof, and no closed Rocq theorem that the machine halts. There is the closest alternative: a
checker proved sound in Rocq and extracted to OCaml, which passed the whole chain on 2026-11-05.** Rocq proves the rule map from the
raw machine and proves that a passing certificate implies the halt in exactly N steps. The evaluation of the certificate
(318,760 chunks, 2,722 core-hours) ran in OCaml, not in the kernel. Eight random chunks and the last chunk were also rechecked in the kernel.

## What is proved, and what is not

| Part | State |
|---|---|
| Rule map from the raw machine, every branch, with exact step counts | **Proved in Rocq.** `theories/Rules.v`, `theories/Map.v` |
| Blank tape to A(6,1) in 35 steps; A(a,a+3) to the halt in a²+7a+41 steps | **Proved in Rocq.** |
| A checker for orbit stretches, covering every jump, the application total and the raw-step total | **Proved sound in Rocq.** `theories/Check.v`, `theories/Cert.v` |
| `cert_ok l f = true` implies the machine halts from blank, and in exactly N steps | **Proved in Rocq.** `theories/Statement.v` |
| `cert_ok` evaluates to true on the 5.37e12-phase chain | **Passed outside Rocq.** Every chunk passed in the extracted OCaml; links and sums checked by `cert/assemble.py`. Not a kernel computation |
| A short proof, with thousands of checks instead of trillions | **Not achieved.** See `research/COMPRESSION.md` |

So the two theorems are implications, and inside Rocq they stay implications. The halt rests on them plus the OCaml run, unless
someone runs the same chunks in the kernel (see "Trusted base").

The statement, from `theories/Statement.v`:

```coq
Theorem bb6_holdout_halts l f : cert_ok l f = true -> halts tm c0.

Theorem bb6_holdout_steps l f :
  cert_ok l f = true ->
  val (fa f) = a_halt ->                               (* 28 * 2^85 - 6 *)
  sum_apps l + val (fapps f) = n_apps ->               (* 674564771793355691986675473 *)
  veqb (vplus (sum_acc l) (facc f)) R_limbs = true ->
  halts_in tm c0 n_steps.                              (* 6448902863343978619509980365051027907909194602118636181048891434378153619188133 *)
```

`tm` is `TM_from_str "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA"`. `c0` and `halts_in` are busycoq's: from the blank tape, n
steps reach a configuration with no transition. N does not count the halting transition; counting it gives the ...134 in
`bb6-orbit/RESULT.md`.

**Axioms.** `Print Assumptions` on both theorems (`demo/Axioms.v`, output in `logs/clean_build.log`) lists only the primitive
63-bit integers of Rocq's standard library and their specifications (`PrimInt63.*`, `Uint63.*_spec`). Nothing else.

## How the checker works

- **Numbers.** Two limbs of primitive ints, 126 bits, with exact specs in Z (`Num.v`). The raw-step total lives in five
  limbs mod 2^315 (`Big.v`, `Vec.v`). A bound from the number of applications alone makes that total exact (`Reach_bound`
  and `cert_steps` in `Cert.v` and `Halts.v`).
- **A sweep over a range of starts.** Along a fixed word every a and b is affine in the start B. A level holds that affine
  state and a range. `lev_ok` says that for every B' in the range and in the residue class mod 4, the map really reaches
  that state from (a0,B'), with the exact application count and cost (`Walk.v`, `Step.v`, `Sweep.v`).
- **Jumps.** Hops in a row until the (reset value, residue) comes back; then `jump` in `Check.v` gives t rounds at once,
  with the cost in closed form.
- **Untrusted division.** `adiv` is only a suggestion. Each use is checked by multiplying back, and no proof looks inside
  it, so the extraction replaces it with a float estimate. The kernel path uses the Rocq definition.
- **Cuts.** The chain is cut at states the C runs sampled every 2^24 phases. Each chunk is an independent call to
  `check_seg`, so the chain runs in parallel and any chunk can be checked alone.

## Build and check

Rocq 8.20.1. Times are from the shared AWS box under moderate load.

```
make                  # the proofs and Print Assumptions: 2 min 8 s on one core, including the busycoq subset
make extract          # extract/check, from extract/Extract.v and extract/main.ml
make demo             # the first chunk proved inside the kernel with native_compute: 1 min 51 s (demo/KernelDemo.v)
```

One chunk with the extracted checker:

```
extract/check seg 6 1 6 20345673609576897    # 19 s, the first chunk of the chain; any line of cert/chunks.tsv works the same way
```

The whole chain: `cert/run_chain.sh WORKERS OUT CHECK_BINARY cert/chunks.tsv`, then `cert/assemble.py CHUNKS SEGLIST SEGDIR OUT/res_*.tsv`. `assemble.py`
checks the links and compares each segment's applications and cost total with `seg.c`.

## The full run

Extracted checker, flambda build, md5 `2e76f48e975338b8331fb467e55ede6d`, on a 128-core c7a.32xlarge, 2026-11-04 06:03Z to
04:37Z on 11-05. Every chunk's result is in `run/out1` and `run/out3` (the `bb6-chain-results` asset), and the assembled output is `logs/assemble.txt`.

| Check | Result |
|---|---|
| Chunks | 318,760 of 318,760 passed, 0 failed, no duplicates, no missing |
| Links | the chunks link from A(6,1) to the last chunk, which reaches the halt form |
| Against `seg.c` | all 712 segments have equal applications and cost total, 0 differences |
| Halt form | A(a,a+3), a = 1083197534374707740536733690 = 28·2^85 - 6 |
| Rule applications | 674564771793355691986675473 |
| Steps from blank, without the halting transition | 6448902863343978619509980365051027907909194602118636181048891434378153619188133 |
| Compute | 2,722 core-hours: 30.7 s per chunk with all cores busy, about 8 times `seg.c`'s 339 |

These totals were computed independently of `seg.c`: the checker proves every jump and sums its own costs. `seg.c` supplied only
the cut points, and a wrong cut point would have failed its chunk. The totals and the halt form equal `bb6-orbit/RESULT.md`.

| Other checks | Result |
|---|---|
| Clean rebuild of the proofs and extraction from these sources, after the run | `extract/checker.ml` identical to the one the run binary was built from, md5 `84b6420601adddc7674050f0c8e75493` |
| 8 random chunks and the last chunk, restated as lemmas and proved in the kernel with `native_compute` (`cert/mkspot.py`, `logs/kernel_spot.log`) | all 9 give the same totals as the OCaml run, about 138 s per full chunk with 9 running at once |
| Wrong end point, or wrong reset value | the chunk fails |
| Start moved by 1 | the chunk still lands on the same end: orbits merge, so this is not a failure |

In the kernel the whole chain would take about 12,000 core-hours, extrapolated from those chunks. That would remove OCaml, `main.ml`
and the extraction from the trusted base. Checking the links and sums in the kernel would also remove `assemble.py`; it has not been done.

## Trusted base

Rocq's kernel with primitive ints checks everything in the theorems.

Evaluating `cert_ok` with the extracted program also trusts:
- Rocq's extraction, the OCaml compiler, and the kernel's own `uint63.ml`;
- `extract/main.ml`, which reads decimal numbers and prints results, and `cert/assemble.py`, which checks links and sums;
- that the run really covered all chunks, which anyone can recheck from `run/` and `cert/chunks.tsv` (the `bb6-chain-results` and `bb6-chunks` assets), chunk by chunk.

`Extract Constant adiv` is not in this list, because the proofs accept any value from it. `extract/stub.c` only satisfies a
link reference the checker never calls.

The flambda build (`extract/build_fl.sh`) needs a separate OCaml 4.14.2 flambda switch and is about 25% faster. The default
`make extract` uses the Rocq switch.

## Credits

The machine framework in `busycoq/` is a subset of `ccz181078/busycoq` branch BB6 (commit 4ea6784), MIT, with its licence files
kept. The machine's rule map is from the bbchallenge community; see `bb6-orbit/RESULT.md`. The traversal and cut points come
from `bb6-orbit/`.
