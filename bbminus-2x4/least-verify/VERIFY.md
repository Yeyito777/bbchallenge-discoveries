# Independent check of BB^-(2,4) < BB(2,4) on tape 110[1]011

> Written before the Rocq proof ("Formal verification" under "Not checked" is out of date). See `../rocq/ROCQ.md`.

## Verdict

**Confirmed, as a machine check.** My own enumeration gives the same 25,594,045 nodes as the ledger. All 10,478,861 halters match the ledger's
step counts, with a maximum of 1,845,977, reached by exactly `2LA2LB0RB---_1RA3RB0RA1LB` and its mirror `2RA2RB0LB---_1LA3LB0LA1RB`. All
15,115,184 other nodes are proved non-halting by my own recurrence check or certificates. So BB_init(2,4,T\*) = 1,845,977 and
BB^-(2,4) <= 1,845,977 < 3,932,964 <= BB(2,4). There are no disagreements in any count, class of halting or step count.

This is not a formal proof, and the same author (me) wrote all the verifier's code. What is left is listed under "Not checked".

I read only RESULT.md, the ledger, `certs/closed/`, the wiki definition and `least/certs/blank_ledger.txt.xz` for the blank-tape gate. I did not read or run `least/code/`.
Everything is in Go and Python.

## Results against the five checks

| # | Check | Result | Log |
|---|---|---|---|
| 1 | Definition and conventions | Applied correctly; see below | `logs/nonorm_compare.txt` |
| 2 | Node set | 25,594,045 nodes each side, sorted lists byte-identical, no duplicates | `logs/compare_walk_ledger.txt` |
| 3 | H records | 10,478,861 of 10,478,861 equal on step count in Go; same in plain Python; maximum 1,845,977, reached by exactly 2 machines | `logs/compare_walk_ledger.txt`, `logs/py_H_all.txt` |
| 4 | C records | 14,529,358 of 14,529,358 detected as recurrent by my detector, which never sees the ledger; separately, all 14,529,358 ledger (start, period, offset) triples pass my criterion | `logs/compare_walk_ledger.txt`, `logs/cverify_ledger_C.txt` |
| 5 | P, W, L records | 585,826 of 585,826 have my own closed certificate, re-checked by a standalone Python checker: 585,826 passed, 0 failed | `logs/T_pycheck.txt`, `certs/T_certs.xz` |
| + | Uncertified machines | None. Every non-halter my walk could not settle by recurrence (580,376) ran 4,000,000 steps without halting, past 3,932,964 | `data/T_walk.sorted.xz` |

Cross-tabulation, my walk against the ledger:

| Mine / ledger | Count |
|---|---:|
| H / H | 10,478,861 |
| C / C | 14,529,358 |
| C / P | 5,410 |
| C / W | 40 |
| U / P | 579,068 |
| U / W | 1,148 |
| U / L | 160 |

The 5,450 C/P and C/W nodes are not a conflict: both say non-halting, and my detector looked longer (start up to 16,384 against the ledger's 4,096).
They also have certificates.

## 1. Definition and conventions

- **Definition.** The wiki defines BB_init(n,m,T) as the longest runtime of a machine that halts on T, and BB^-(n,m) as the minimum over T. T\* is a legal T, so
  BB^-(2,4) <= BB_init(2,4,T\*). The inequality needs only that value and the champion's run. My simulators agree on 3,932,964 for
  `1RB2LA1RA1RA_1LB1LA3RB---` on blank.
- **Tape.** `110[1]011` is cells -3..3 = 1 1 0 1 0 1 1 with the head on cell 0, state A. The root reads (A,1), so it halts at step 1, and the ledger's first record agrees.
- **Step count.** The halting step is counted, consistent with BB(2,4) = 3,932,964 and with the wiki's BB^-(1,m) = 1.
- **Tree argument.** Take any complete machine M. Walk the tree by adding M's entry each time the partial machine hits an undefined entry. Either M is undefined there, and it
  halts at that node's step, or the path ends at a non-halting node whose run M copies forever. A node with 7 defined entries needs no children, since its child has none undefined.
- **State normalisation.** There is none to get wrong. With two states, children always offer A and B, and A is the fixed start state.
- **Symbol normalisation on this tape.** Sound, and tested exhaustively. Only 2 and 3 are interchangeable, because 0 and 1 are on the tape. I walked the full unnormalised tree, where every
  node offers all four writes: 51,185,809 nodes. Relabelling 2 and 3 by first use maps them onto exactly the 25,594,045 normalised nodes, 2,281 once and 25,591,764 twice.
  2,281 is exactly the number of nodes that write no 2 or 3. There were no disagreements on class or step count. In that run, nodes already known as non-halting were simulated to 100,000 steps
  and the rest to 2,000,000.
- **Mirror.** No left/right reduction is used. T\* is symmetric, and in my walk every node's mirror exists with the same class and step count: 0 exceptions of 25,594,045.

## 2 to 4. Walk and recurrence

`code/walk` is a depth-first walk with no ledger input. It stops a node at a halt, at a recurrence, or at 4,000,000 steps. Because that limit is above 1,845,977 and above the champion's count,
a longer halter would have shown up as an H node with children and changed the node set.

Recurrence criterion: at t0 the machine is in state q. Over the next p steps it reads cells [lo, hi] and returns to q displaced by d, with the cells [lo+d, hi+d] then equal to [lo, hi] at t0.
If d > 0, every cell above hi must be blank at t0; if d < 0, every cell below lo. By induction each later period repeats the first, so the machine never halts.
`code/cverify` applies this to the ledger's own triples and then runs 5 more periods. `code/check/py_sim.py` is a separate Python version, run only on a sample:
100,000 random C nodes plus 30,000 with start >= 512 or period >= 64, 0 failures (`logs/py_C.txt`).

## 5. Non-halting certificates

I wrote this decider from the problem, without the ledger's parameters. Each tape side is read by a finite automaton from infinity towards the head. A push follows an edge; a pop goes to every
recorded predecessor. A certificate is the edge sets plus a set of abstract configurations (left state, control, head cell, right state). `code/check/check_cert.py` holds the theorem and checks each
certificate from its final sets alone: the start config is in the set, it is reached from a blank cycle, no config has an undefined transition, and each config's successors are all in the set.
It knows nothing about how the automata were built, so a decider bug cannot pass unless the set really is closed.

| Automaton family | Machines |
|---|---:|
| Last cells only | 566,526 |
| Last cells plus per-cell history | 12,306 |
| Run list, anchored at first nonblank cell | 6,798 |
| Run list, anchored, limited depth | 158 |
| Run list, absolute grid, limited depth | 22 |
| Run list, absolute grid | 8 |
| Run list with symbol parity, anchored, limited depth | 8 |

Total 585,826, with 59,155,426 configurations; the largest is 100,176, for `2LB0RA3RA2RA_3RA---0LA3LB`. The set of families was tuned by looking at which machines stayed open, and the ledger's parameter tables
gave hints on what to try. The checker does not depend on any of that.

Their four explicit sets in `certs/closed/` also pass my checker, with sizes 702, 702, 8,112 and 7,556 (`logs/check_their_closed.txt`). Mine needs 436 for `1LB1LA1RB---_3RA2LB0RA1RA` and 24,147 for
`1RB2LA3LA0RA_1LA---2RB2RA`, with different automata. "Hardest" therefore depends on the abstraction; it is not a property of the machine.

Tests of the decider and checker:

| Test | Result | Log |
|---|---|---|
| Blank tape walk | 718,225 nodes, identical to their blank ledger's node set; 240,465 H, 0 step mismatches; top list as in RESULT.md | `logs/blank_gate.txt` |
| Blank tape certificates | 55,094 of 55,094 non-recurrent machines decided and passed | `logs/blank_U_pycheck.txt` |
| Decider on halters (must decide none) | 0 of 240,465 on blank; 0 of 323,410 on T\* (all H >= 100 steps plus 300,000 random), 0 of 1,174 on T\* (all H >= 500 steps) with all 1,281 families | `logs/decider_on_halters.txt` |
| Real-run tracking: map each real config of a 20,000-step run into the certificate | 18,572 certificates (all run-list ones and every 50th of the rest), 0 failures | `logs/dyn_check.txt` |
| Damaged certificates, 216 sampled | Dropping a config, half the configs or an edge, or undefining a transition: 0 accepted of 216 each | `logs/mutation_checker.txt` |
| Same set with one write symbol changed | 13 of 216 accepted; a pass claims the altered machine never halts, and all 13 ran 3,000,000 steps without halting | same |
| Deliberately broken decider (blank tail with no predecessor) | It "decided" 2,987 of 3,000 halters; the checker rejected all 2,987 | `logs/broken_decider.txt` |
| Long runs of the 18 machines with the hardest or largest certificates | No halt in 1e10 steps | `logs/longrun_hard.txt` |

## A bug of mine

My first run-list code on absolute grids had that same blank-tail bug: tail states without a predecessor, which lost configurations. It "decided" all of a 19,300-machine batch, including the hardest machines,
which looked wrong. I fixed it before any reported run. The broken-decider test above recreates the same fault by deleting the block in `code/decide/main.go` that adds the tail's blank edges (that throwaway variant was not kept). The internal Go re-check did not catch it, because that re-check did not look at the start path; the Python checker does.

## Disagreements and remarks on RESULT.md

- No disagreement on any number I checked: node count, H, C, P+W+L totals (with the 5,450 reclassified above), top halters 1,845,977; 217,204; 167,375; 158,767; 122,500, count of H >= 500 (1,174), closed set sizes, blank gate.
- RESULT.md calls two machines the "hardest non-halters". That holds only for its own abstractions, as noted above.

## Not checked

- **Their P, W and L parameters.** The ledger format is defined in `least/code/`, which was off limits, so I did not replay those parameters. I replaced them with my own certificates. So this confirms that those
  machines do not halt, not that their parameters are correct certificates. Only their 4 explicit sets were checked directly.
- **Python on all C records.** Python ran on 130,000 C nodes only. The full set has two Go checks: the walk's own detection and the ledger-triple check. A full Python run would cost about 8 CPU hours and I judged it not worth it.
- **Formal verification.** No Rocq or other proof assistant was used. The soundness theorems are short arguments stated in `code/check/check_cert.py` and here, not machine-checked ones.
- **Independence.** Independent of their code, but my tools share one author and one design for the abstraction. The Python checker and simulators are separate code from the Go ones.
- **The rest of RESULT.md.** I did not check the other-tape census (`kills.txt`), the periodic backgrounds or the 8-instruction machine remark. They do not affect this claim.
- **Literature.** I did not check for later work than the corpus snapshot.

## Compute

About 3 hours, on 2 to 5 cores of two ordinary machines.

## Rerun

```
cd code/walk && go build -o walk . && cd ../decide && go build -o decide . && cd ../cverify && go build -o cverify . && cd ../nonorm && go build -o nonorm . && cd ../longrun && go build -o longrun . && cd ../..
# Certificate check only, without trusting any Go code (about 5 minutes):
xz -dc certs/T_certs.xz | python3 -I code/check/check_cert.py '110[1]011'
python3 -I code/check/check_cert.py --closed ../least/certs/closed/*.txt
# Walk (about 3 CPU hours), then compare with the ledger:
code/walk/walk -tape '110[1]011' -limit 4000000 -lincap 32768 -out OUT -workers 2 -frontier 2000
# Certificates from scratch (about 5 minutes on 3 cores):
code/decide/decide -tape '110[1]011' -fams code/families.txt -workers 3 -dump D -dump-every 1 < NAMES > OUT
# Unnormalised tree (feed it the non-halter names):
code/nonorm/nonorm -u NAMES -limit 2000000 -short 100000 -o OUT -workers 2
```

- `data/T_walk.sorted.xz`: my class for every node.
- `data/T_decide.out.xz`: the family and set size for each certified machine.
- `certs/T_certs.xz`: all 585,826 explicit certificates.
