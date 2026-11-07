# The 16-machine group: one orbit, one list map

Date 2026-11-05. Labels: **[M]** measured by my code, **[E]** my estimate or argument, not proved.

## Bottom line

- **Not settled, and I do not expect it to settle soon.** There is no reachable halt in sight and no certifiable non-halting argument.
- **All 16 machines follow one stack orbit.** The classes of 8, 6 and 2 give the same stack (rule table below); only state names, raw step counts and the last small run differ **[M, `rawlist` on all 16]**.
- **The map is short and exact.** Five rules on a stack of numbers. It agrees with the raw machine on every check so far, including every halt in random tests **[M]**. No fitting is left in it.
- **The halt has an exact form, now proved.** A machine in this group halts exactly when an event I call a top event has P + 2 = 2^k. Rocq proves both directions and the map itself from the raw table, for all 16, with no axioms: `../rocq/ROCQ.md`. It was first found and tested: every raw halt in the random tests below was predicted, none predicted and missed **[M]**.
- **The odds are tiny.** P has reached 1.09e10 with no hit, and P grows quickly. A rough model gives about 2e-10 expected hits from here **[E, heuristic]**.
- **Why this is not a proof target.** P + 2 hits powers of two at chance level from random stacks, so no congruence blocks it. Proving non-halting means proving a sparse sequence avoids powers of 2. That looks Collatz-like too, though the object is much simpler than the 14-machine family.

## The list map

The tape is a list of unary runs `1^a1 0 1^a2 0 … 1^ak`. Machine moves, for `1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF`:

| Move | Effect |
|---|---|
| A walks right over 1s; `<A> 0 1 1 → 1 0 1 <A>` | crossing a separator moves it right one cell |
| F walks left over 1s; `<F> 0 1 1 → 1 0 1 <A>` | the same shift, then A goes right |
| A at `00` or blank | turns into F going left, leaving a `00` marker |
| `<A> 0 1 0 1` | A crosses a run of length exactly 1: E reads 1, **halt** |

Those moves zigzag: a `00` marker sits at the right end of a run r, with left neighbour p and right neighbour y. Each round does p+1, r−2, y+1 **[M]**.

**State.** A stack a_1 … a_m above a fixed tail that cycles (6,4,1) → (8,5,·) → (8,6,3). (The classes with last value 2 cycle (6,4,2) → (8,5,1) → (8,6,4), with one extra (8,5,3) step in the class of 2.) One step of the map runs one pass of that tail cycle.

**One step.** Set r = a_m + 2 and i = m, then:

```
while true:
  if r is odd:   a_(i-1) += (r+3)/2;  a_i = (r+9)/2;  stop
  if r is even:  a_i = r/2 + 2
                 if i = 2:  top event with P = a_1 + r/2
                 else:      r = a_(i-1) + r/2 - 2;  i = i-1
```

**Top event.** Starting from P, replacing a_1:

```
while P is even:
   if P = 2: HALT
   push P/2 + 1 just left of the entries;  P = P/2 - 1
(P odd): new leftmost two runs (P+1)/2, (P+1)/2 + 3
```

So a top event halts exactly when P + 2 is a power of 2 (k ≥ 2). Other P only lengthen the stack.

**The orbit.** The stack reaches (10, 9) above the tail almost at once. Each step adds 8 cells of width. Each run is a level, counted from the right. Levels pass carries to the left only: a level never depends on anything to its left. A carry reaches the top about once per 2^m steps, so top events are rare:

| Step | m | P | v2(P+2) |
|---|---|---|---|
| 39 | 6 | 104 | 1 |
| 335 | 8 | 1,290 | 2 |
| 591 | 11 | 647 | 0 |
| 2,639 | 12 | 7,146 | 2 |
| 26,767 | 15 | 93,998 | 4 |
| 223,375 | 20 | 281,082 | 2 |
| 3,986,639 | 23 | 6,578,054 | 3 |
| 119,658,935 | 27 | 283,561,616 | 1 |
| 940,032,183 | 29 | 4,855,353,465 | 0 |
| 1,006,974,159 | 30 | 4,419,000,675 | 0 |
| 2,311,395,767 | 31 | 7,939,115,924 | 1 |
| 3,285,731,471 | 33 | 10,931,368,376 | 1 |

Earlier events: P = 23, 21, 24. The run went to 2e10 steps with m = 35 and no further top event **[M, `lm.c`]**. Only P + 2 = 2^k would halt; the largest v2 seen is 4.

## Verification

| Check | Result |
|---|---|
| Raw machine from blank against the map, all 16 machines (`rawlist.c`, plain array, no acceleration) | 26,767 of 26,767 stack states, through 3e10 raw steps, width about 214,183, 7 top events. Identical stack on all 16. `g16verify.txt` |
| Random start stacks against raw, all 16 (`rawlist2.c`, 200 stacks each, first run may be small) | 75,032 of 75,032 stack states, 482 top events, 14 raw halts, all predicted, none predicted and missed. The same numbers on each machine. `g16verify.txt` |
| Same test, larger on the representative | 400 stacks: 154,272 states, 1,031 top events, 15 halts, all predicted |
| Direct: top-stage tape with chosen P on raw | P = 2, 6, 14, 30, 62, 126 all halt, leaving runs 3, 3, 4, 8, 16, … on the left. The other P up to 25 did not halt within the 3 events printed |
| Event stream from `gensim` against the map | 1,992 of 1,992 states |

The halting criterion holds on every test above, and is now a theorem (`../rocq/ROCQ.md`). Small runs were tested down to first run 1 and other runs 3.

## Structure, and why it does not close

**Lower levels are periodic.** The rule contracts: each processing halves a level's value, so a level driven by a periodic input becomes periodic. Measured on 2^22 steps **[M]**:

| Level from the right | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Period (steps) | 4 | 8 | 32 | 64 | 128 | 512 | 2048 | 4096 | 8192 | 32768 | 131072 | 655360 |
| Carries left per period | 2 | 1 | 2 | 2 | 3 | 7 | 14 | 14 | 15 | 33 | 68 | 175 |

**A trap would be a proof, and it does not happen.** If a level's periodic orbit has every r odd, no carry ever leaves it, the level above grows forever, and the machine is provably non-halting. Level 0 has such a fixed point: a_m = 11 stays 11. About 12% of random stacks reach no top event within 20,000 steps, which fits traps like this **[M, cause not checked for each]**. The real orbit avoids them: its level 0 sits on the 4-cycle 7, 9, 10, 8. An all-odd orbit needs an integer fixed point of a map with slope 2^-N, where N is the number of carries per period, so it is available about 1 time in 2^N **[E]**. With N already 175 at level 11, I expect no trap **[E]**.

**The top levels are not periodic in practice.** Periods grow about 2^(1.5 j), faster than the time to reach that level. So the top levels at any moment are still in their first period, and P depends on all of it. I found no closed form for P_n.

**No congruence blocks the halt.** From 35,000 random stacks (the other 5,000 of 40,000 reached no top event in 20,000 steps), P + 2 is a power of two at about chance rate in each size band, for example 188 hits against about 122 at chance for 2^7, 53 against 24 at 2^8 **[M, `ens.py`]**. Random stacks are not the real orbit, so this rules out simple congruences only.

**Rough odds, a heuristic only.** A top event with P of b bits hits a power of two with chance about 2^-b. P has reached 1.09e10. It usually rises several times per event, though it can dip slightly. That gives a sum near 2e-10 for all future events **[E]**.

## What would settle it

- **A halt:** none in sight. More running gives almost nothing: the odds above are the whole remaining chance. `lm.c` does about 8e7 map steps per second. A hierarchical jump using the periodic levels could reach P near 2^60 to 2^90 **[E]**, but the odds fall as fast as the reach grows.
- **A proof:** it needs to show that P_n + 2 is never a power of 2, for one explicit sequence. That needs control of the top levels I do not have. If someone found a closed form for P_n, this would become easy.
- **Rocq reduction, done:** "these 16 machines halt iff the stack orbit has P + 2 = 2^k" is proved in `rocq/g16`. It settles none of them, but any answer about the one sequence now settles all 16 at once. The kernel also checks the first 30,000 stacks.

## Files

`lm.c` (fast map), `listmap.py` (map), `rawlist.c` (raw against map, from blank), `rawlist2.c` (raw against map, random stacks, halting criterion), `period.py`, `outputs.py` (level periods), `ens.py` (ensemble), `lsim.py`, `ltrace.py` (raw traces), `g16fam.txt`, `g16fam2.txt` (machines with flags). `../g16_members.txt` has the 16 machines.
