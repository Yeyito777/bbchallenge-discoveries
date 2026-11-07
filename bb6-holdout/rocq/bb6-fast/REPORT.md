# bb6-fast report

> The C prototypes and benchmarks mentioned below are not included in this repository.

Goal: a Rocq proof of the BB(6) holdout's halt with no extracted code, that fits a desktop. Both `halts tm c0` and the exact count `halts_in tm c0 n_steps` are done.

**Result (exact count):** `Theorem bb6_holdout_steps : halts_in tm c0 n_steps.` is proved and checked, for `Statement.v`'s `n_steps`. All 707 jobs passed in the kernel: 441 core-hours, 5 h 50 min on the 128-core box (80 jobs at a time), at most about 2.7 GB per job. The assumptions are the primitive ints and arrays only.

**Result (halting):** `Theorem bb6_holdout_halts : halts tm c0.` is proved and checked. All 313 jobs passed in the kernel: 275 core-hours, 2 h 40 min on 128 cores, at most 1.55 GB per job. That is about 10x below the old checker's OCaml run (2,722 core-hours) and about 44x below running it in the kernel (about 12,000). On an 8-core desktop it scales to about 34 hours and 13 GB (not measured on a desktop).

## Costs (measured unless marked)

| Checker | Rate | Whole orbit |
|---|---|---|
| Old checker, extracted OCaml | | 2,722 core-hours (run) |
| Old checker, kernel | 138 s/chunk | about 12,000 core-hours (extrapolated) |
| Flat limb checker, kernel, flambda | 42 s/chunk | about 3,700 core-hours (extrapolated) |
| Block lemmas with exact counts, kernel, flambda, no proofs | 4.3 s/chunk at 2^90.8 | about 400 core-hours (extrapolated) |
| Block lemmas, `halts` only, proved, kernel, flambda | 3.1 s/chunk on average | **275 core-hours (run)** |
| Block lemmas with exact counts, proved, kernel, flambda | 5.0 s/chunk on average | **441 core-hours (run)** |
| `halts` only, kernel VM instead of `ocamlopt` | 238 s for one 16-chunk window, vs 40 s | about 1,500 core-hours (extrapolated) |

Where the time goes in the run: the first job (the first 1024 chunks) took 117 min, jobs near chunk 200,000 took 14 to 21 min, the median was 57 min.

The samples behind the 250 core-hour estimate, cold 16-chunk windows at a 2M table limit, by position in the orbit (the run came in 10% above the estimate):

| Chunk | 2,000 | 10,000 | 40,000 | 80,000 | 120,000 | 160,000 | 200,000 | 250,000 | 290,000 |
|---|---|---|---|---|---|---|---|---|---|
| Time (s) | 59 | 62 | 53 | 42 | 36 | 41 | 8 | 41 | 38 |

## Table size, time and memory

256-chunk windows at two scales, kernel, flambda. The table is cleared when full.

| Limit (entries) | Time at 2^90.8 (s) | Time at 2^80.5 (s) | Peak memory |
|---|---|---|---|
| 250k | 878 | 868 | 1.15 GB |
| **500k (chosen)** | 696 | 814 | 1.5 GB |
| 1M | 652 | 887 | 2.2 GB |
| 2M | 655 | 966 | 3.2 GB |
| 4M | 673 | 1040 | 5.9 GB |
| 8M | 700 | 1080 | 10 GB |

Past about 1M a bigger table does not help: reuse is mostly local, and GC cost grows. These runs shared a loaded box, so differences of a few percent mean nothing. OCaml GC settings (minor heap 32M to 512M words, space overhead 120 to 250) changed time by under 3% on 64-chunk windows, so the defaults stay.

The earlier 4.4 GB at 600k entries was a leak: the empty table was a global constant, so the persistent array's history kept every old version of every tree alive. The table now starts from a fresh array.

## What was tried

- **Flat limb checker.** About 3.3x from a plain rewrite. Kept as the reference; not enough alone.
- **Block lemmas.** A block lemma covers every state in a region of (b, S, g) and all sweeps of a word prefix. Regions are exact integer lines, pulled back through two letters with a margin proved as a lemma (`HLines.v`). The fixed-point point only picks what to try. This is the design that shipped.
- **Merged paths for `halts` only.** The idea was to merge states by the sweep's outcome rather than its shape. Measured dead: the outcome intervals are about the same as the shape intervals (ratios 1.0 to 1.15). Dropping the cost polynomials alone gave about 2.2x.
- **Exact-shape reuse.** Bounded at about 90x on 8e9 phases, whatever the table size.

## What is trusted

See `README.md`. In short: the Rocq kernel, `ocamlopt` under `native_compute` (the VM route avoids it, about 6x slower), and the primitive integer and array axioms. Soundness does not depend on the table, the cut points or any fixed-point number: a wrong one makes a job fail.

## What remains

The exact-count theorem `halts_in tm c0 n_steps`. The regions, pull-backs, dominance, table and top recursion carry over. Block lemmas need to carry application counts and cost polynomials, with their proofs. The unproved prototype ran about 2x slower than `halts` only.

Status: every part of the exact-count proof is proved, with no admits (`XCost`, `XCore`, `XAbs`, `XBand`, `XTop`, `XFinal`). The chain composes with the jobs stood in by axioms.

Checked in the kernel against the old run, count and all five cost limbs: chunk 0; 16-chunk windows at chunks 2000, 120000, 200000 and 290000; the halting chunk. All match exactly.

Speed:

| Sample | Exact count (s) | `halts` only (s) |
|---|---|---|
| Chunk 0 | 110 | 30 |
| 16 chunks at 2000 | 111 | 59 |
| 16 chunks at 290000 | 84 | 38 |

That is about 2x overall. The full run took 441 core-hours: 1.6x the `halts` run, which had used all 128 cores on the same type of box.

Two speedups were tried:
- Turning literal constants into machine-int lists: 952 to 7 s on a chunk.
- A fixed five-limb multiply instead of the generic limb lists: 1.4 to 2x slower, because most values are one or two limbs. Reverted.
