# BB^-(2,4) < BB(2,4): first proved case of BB^- differing from BB

> Written before the independent check and the Rocq proof, so "No human or formal review yet" and the "Caveats" are out of date on that point. See `../least-verify/VERIFY.md` and `../rocq/ROCQ.md`.

## Claim

Let T\* be the tape `110[1]011`: cells ... 0 0 1 1 0 **1** 0 1 1 0 0 ..., head on the bold cell, start state A, blank elsewhere.
Every 2-state 4-symbol Turing machine started on T\* either never halts or halts in at most 1,845,977 steps, and two machines (mirror
images) reach exactly that count. So BB_init(2,4,T\*) = 1,845,977. Since the champion `1RB2LA1RA1RA_1LB1LA3RB---` halts on the blank
tape in 3,932,964 steps, BB^-(2,4) <= 1,845,977 < 3,932,964 = BB(2,4). The inequality needs only the champion's run plus the exhaustive
result on T\*, not the Coq proof of BB(2,4). BB^-(2,4) itself is not determined: only this upper bound.

This was machine-checked here only. No human or formal (Rocq) review yet.

## Definitions and conventions

From `knowledge/wiki/pages/Main/Least_Busy_Beaver.wiki` and `knowledge/discord/general/chat/2025-02-15--2025-02-16.md`:
BB_init(n,m,T) is the longest runtime of an n-state m-symbol machine that halts on tape T, and BB^-(n,m) = min over T of BB_init(n,m,T).
The tape includes a fixed head position; the machine always starts in state A; infinite tapes are allowed (T\* is finite).
A machine halts by reaching an undefined transition. The halting step is counted, as in BB(2,4) = 3,932,964; not counting it gives
1,845,976 against 3,932,963, so the inequality does not depend on that choice.

## Exact numbers on T\*

Search space: 25,594,045 normalised nodes, each with one record in the ledger.

| Record | Count | Meaning |
|---|---:|---|
| H | 10,478,861 | reaches an undefined transition at the stated step; has children unless 7 transitions are defined |
| C | 14,529,358 | Lin recurrence (cycler or translated cycler) |
| P | 584,478 | n-gram closed position set, optionally with per-cell or head history |
| W | 1,188 | repeated word list closed graph |
| L | 160 | closed language over run-compressed blocks, optionally with symbol-count parity |

Top halters: 1,845,977 `2LA2LB0RB---_1RA3RB0RA1LB` and its mirror `2RA2RB0LB---_1LA3LB0LA1RB`; then 217,204; 167,375; 158,767; 122,500.

The two hardest non-halters, each with its mirror image, are in `certs/closed/` as explicit automata and closed sets:
- `1LB1LA1RB---_3RA2LB0RA1RA`: 702 abstract configurations. It behaves like a ternary counter. The closed set needs the parity of the
  number of 3s on each side of the head, plus 2-cell blocks anchored at the first nonblank cell.
- `1RB2LA3LA0RA_1LA---2RB2RA`: 8,112 abstract configurations (its mirror 7,556, because the block grid is not mirrored). No halt in 1e11
  steps. Certificate parameters K=4, M=3, block 4.

The descriptions of behaviour are informal; the certificates are what counts.

## Method

1. Enumerate partial machines on T\* (`code/tree.c`). States are in first-use order. Symbols not on the tape and not yet written are
   interchangeable, so only the lowest is tried: on T\*, 2 and 3 are the free symbols. No left/right reduction is used, though T\* is
   symmetric (the pitfall in `knowledge/discord/general/chat/2025-02-16--2025-02-17.md`).
2. Prove survivors non-halting with `code/cps.c`, `code/repwl.c`, `code/runlang.c`; simulate what is left to the threshold; repeat on
   any children.
3. Verify with `code/check` (Rust, separate code): it walks the normalised tree itself from the empty machine using a two-stack simulator,
   re-derives children, requires exactly one ledger record per node, and re-verifies each record.

## Gates reproduced

- Blank tape, full pipeline, both implementations: 718,225 nodes, no holdouts, top list 3,932,964 (champion), 7,195, 6,445, 6,445, 2,351,
  1,021, 1,001, plus mirrors, matching `knowledge/wiki/pages/Main/BB(2,4).wiki`. So the pipeline independently reproduces
  BB(2,4) = 3,932,964. `certs/blank_ledger.txt.xz`, `logs/check_blank.txt`.
- Champion on the candidate tapes: blank 3,932,964; `[2]` and `[3]` 3,932,963; `1[0]` 3,932,962; `2[0]` and `3[0]` 608.
- 2x3 tree: 38 on blank; 47 on `[1]`, the corpus machine `2LA2RB1RZ_1RA2RA1LB`.

## Checks on T\*

| Check | Result | Log |
|---|---|---|
| Rust verifier over the whole ledger, threshold 1,845,978 | 25,594,045 nodes, 0 errors, PASS | `logs/check_110a1b011.txt` |
| Node counts, C enumerator against Rust walk | identical | same |
| Mirror test: T\* is symmetric, so H/non-H and step counts must match under mirroring | 0 asymmetric of 25,594,045 | `logs/randtest_mirror_110a1b011.txt` |
| Explicit closed sets, standalone `code/check_closed.py` | 4 of 4 pass; C, Rust and Python report the same set sizes (702, 702, 8,112, 7,556) | `logs/check_closed.txt` |
| Top halter counts, Rust and plain Python simulators | 1,845,977 for both | `logs/halt_check_python.txt` |
| Random machines, plain Python, not normalised (60,000): their normalised forms in the ledger with the same step counts | 29,659 of 29,659 | `logs/randtest_mirror_110a1b011.txt` |
| Deciders run on all 1,174 machines on T\* that halt at step >= 500: must decide none | 0 decided by CPS, RepWL or run-language grids | `logs/longcheck_soundness_110a1b011.txt` |
| Direct simulation of non-halting records | 585,826 P/W/L machines to 2,000,000 steps and the 1,348 W/L machines to 300,000,000 steps: none halted | same |
| Regeneration from nothing with `code/prove2.sh`, then the Rust verifier | 0 holdouts; same class counts; PASS; this is the published ledger | `logs/stages_110a1b011.txt`, `logs/ledger_sha256.txt` |
| Verifier mutation test on the blank-tape ledger: wrong counts, missing records, halters claimed non-halting are rejected | as expected | `logs/mutation_test_blank.txt` |

## A bug that was caught

The first full ledger for T\* passed the Rust verifier and was wrong. `repwl.c` built its initial left stack with a block straddling the
tape's left edge, and I had written the same mistake into the Rust check, so both agreed. 61 machines were falsely called non-halting,
including the mirror of the top halter. The mirror test caught it. It is fixed in both tools, and all records on T\* were regenerated
afterwards. `kills` results are unaffected, since they are halting counts. The lesson for review: the two implementations share an author
and could share another logic error. That is why the mirror, soundness and long-simulation tests above exist, and why independent
reimplementation of the deciders is the most useful next check.

## Other tapes: T\* is close to unique among small tapes

The scout's premise was too optimistic: "the champion runs 608 steps on `2[0]`" is true, but other machines run far longer. Symbols 1, 2
and 3 are interchangeable on a tape class, so `1[0]`, `2[0]`, `3[0]` are one class and `[1]`, `[2]`, `[3]` another. Extra marks usually
*raise* BB_init above BB(2,4). All four scout tapes fail, each with a halter above the champion's count (`certs/scout_tapes.txt`):

| Tape | Machine | Steps |
|---|---|---|
| `[2]` | `2LB---1RB3RA_1RA3LB1LB1RB` | 5,391,646 |
| `[3]` | `3LB1RA---2RB_2RA2RB1LB2LB` | 5,391,646 |
| `1[0]` | `0RB2LA1RA2RA_1LB2LA3RB---` | 56,946,968 |
| `2[0]` | `0RB2RA1LA1RA_2LB3RB1LA---` | 56,946,968 |

Census of finite tapes up to radius 3, one class per relabelling of {1,2,3} and mirroring: 1,451 classes (`code/tapes.py`).
- 1,449 have a machine at or above the champion's 3,932,964 (`certs/kills.txt`, verified by the separate Rust simulator `killcheck`).
  The blank tape is the only one that merely ties.
- All 107 classes of radius up to 2 fail this way, except the blank tie.
- T\* is proved below the champion.
- `110[0]023` is undecided: best halter so far 3,932,944, with 1,299 machines open at 1e9 steps.

Periodic backgrounds also fail: `(0123)[0]123(0123)` 5,315,589; `(01)[0]1(01)` 13,034,342; `(1)[0](2)` 15,721,562; `(0)[0](1)` 11,104,225.
Long halters on nearby tapes reach 5.3e9 steps (`01[1]23`). One 2-state core, `---3RB2RB3RA_2LB1RA3LB0RB`, runs 3,545,123,812 steps there:
it is rows C and D of the known 8-instruction machine `1RB---------_2RC---------_3LC1RD0RC2LC_------2RD3RC` (3,545,123,827) with 2 and 3
swapped, the tape supplying what that machine's first two rows write. This shows how hard tapes are to beat; lower values than 1,845,977
may exist on larger tapes.

## How to rerun and check

```
cd code; for f in tree cps repwl runlang; do gcc -O2 -fopenmp -I. -o $f $f.c; done
cargo build --release --manifest-path check/Cargo.toml
# Check the published ledger (about 26 minutes on 3 threads; needs about 5 GB):
xz -dc ../certs/ledger_110a1b011.txt.xz > /tmp/ledger.txt
CHECK_THREADS=3 check/target/release/check '110[1]011' 1845978 /tmp/ledger.txt
# Standalone hardest cases, top halters and the tape table:
python3 -I check_closed.py ../certs/closed/*.txt
check/target/release/killcheck < ../certs/kills.txt
# Single certificate:
check/target/release/check --one '110[1]011' L 1RB2LA3LA0RA_1LA---2RB2RA 4 3 4 0 0
# Regenerate the ledger from nothing (LEASTBIN = folder with the binaries):
LEASTBIN=$PWD OMP_NUM_THREADS=4 bash prove2.sh '110[1]011' 3932964 /tmp/thm1
```
Ledger format is at the top of `code/check/src/main.rs`.

## Caveats

- Not formally verified. A Rocq version on the Coq-BB5 deciders would settle trust; n-gram CPS and RepWL are already there, while the
  run-language closure (160 machines) would need a new verified decider, or conversion to its regular-language form.
- Only an upper bound on BB^-(2,4).
- `tree.c` and the Rust walk share the normalisation design, tested by the random-machine test. The argument itself is short: relabelling
  symbols absent from the tape, or states, gives an isomorphic run.
- Not posted anywhere. The corpus snapshot is 2026-10-29; I did not check for later work.

## Credit

- Definition, name and first certificates: racheline, Shawn Ligocki and others in `knowledge/discord/general/chat/2025-02-08--2025-02-15.md`,
  `2025-02-15--2025-02-16.md`, `2025-02-16--2025-02-17.md`. Shawn Ligocki named 2x4 as the best chance; racheline left it open.
- n-gram CPS and RepWL: mxdys, Coq-BB5; `knowledge/wiki/pages/Main/Repeated_Word_List.wiki`, `knowledge/discord/deciders/chat/2024-04-05--2024-05-24.md`.
- BB(2,4) proof and pipeline history: `knowledge/discord/bbxy/chat/2024-07-30--2024-08-30.md`.
- Automata approach: Finite Automata Reduction, `knowledge/wiki/pages/Main/Finite_Automata_Reduction_(FAR).wiki`.
- 8-instruction machine and step count: scout note `scout-smalltm.md` and the corpus it cites.
