# `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` halts from the blank tape

> **Update 2026-11-05:** the totals are now independently confirmed. A Rocq-proved checker, extracted to OCaml, checked every jump of the chain in 318,760 chunks (2,722 core-hours, 0 failures), carried its own application and step totals, and reproduced the halt form and every number below; all 712 segments match `seg.c`. See `../rocq/bb6/ROCQ.md`. Since then the halt is also a closed Rocq theorem, proved in the kernel: see `../rocq/bb6-fast/README.md`. This file and that run remain the evidence for the exact step count. Host names and one name were changed when staging.

**Status: computational result, not a formal proof.** The rule map is tied to the machine in Lean, but the run that reaches the halt was done in C and is not checked in Lean. The exact totals come from one implementation, with a second one checking samples. Details are under "What is confirmed and what is not".

## Claim

Started on the blank tape, the machine reaches A(6,1) after 35 steps. Here A(a,b) = `0^inf 1^a A> 1 1^b 01 0^inf`. Iterating the corrected rule map from A(6,1) reaches the halt form A(a,a+3) after 674564771793355691986675473 rule applications, with a = 28·2^85 − 6. No earlier halt occurs and the orbit never enters the family A(4n+2,8n+22). From there the machine halts.

| Quantity | Exact value |
|---|---|
| Halt form A(a,a+3) | a = 1083197534374707740536733690, b = 1083197534374707740536733693 |
| Last reset state | A(22, 28·2^86 − 286) = A(22, 2166395068749415481073467106), followed by 85 doubling rules |
| Rule applications from A(6,1) to the halt form | 674564771793355691986675473 |
| Raw steps from blank, not counting the halting transition | 6448902863343978619509980365051027907909194602118636181048891434378153619188133 |
| Raw steps from blank, counting the halting transition | 6448902863343978619509980365051027907909194602118636181048891434378153619188134 |
| Ones on the final tape | 1083197534374707740536733699 (a + 9) |
| Final tape | `0^inf 1^5 (10)^1083197534374707740536733693 D>1 0^inf`: state D reading 1, on the rightmost 1 |

The step count is about 6.45×10^78. By BB(6) standards this is small, so the machine is not a champion. It only removes a holdout. The cryptids docstring estimates a halt near 10^110 steps from its hazard heuristic; the real halt comes earlier.

## The map

For even a ≥ 6:
```
b == a+3                  halt
b >  a+3                  (2a+6, b-a-3)                                    D
b == 1                    a%4==2 ? (6, a+7)  : (22, a-2)                   p, q
b == 3                    a%4==2 ? (6, a+13) : (a+8, 2)                    r, s
odd b >= 5, u=(a-b+5)/2   u==2 ? (6, a+b+2) : u odd ? (a-b+11, 2b-4) : (a-b+19, 2b-8)      t, u, v
even b, h=(a-b)/2         h odd ? (6, a+b+7) : (22, a+b-2)                 w, x
```
Raw steps per rule: D a²+3a+15; p (13a+142)/2; q (13a+406)/2; r (21a+282)/2; s (11a+88)/2; t a²+5a+41; u b²+(11a−5b+85)/2; v b²+(19a−13b+231)/2; w b²+(13a−3b+150)/2; x b²+(13a−3b+414)/2. From A(a,a+3) to the halt: a²+7a+41 steps, leaving a+9 ones.

## Method

- **Sweeps and phases.** The orbit is a chain of sweeps, each running from a reset state (a0,B) with a0 in {6,22} to the next. Along a fixed branch word every a and b is affine in B with integer slope. So the word repeats while B stays in its residue class mod 4 and below a computed bound, and whole cycles can be jumped exactly. One jump is a "phase". This needs exact integers: `__int128` for values, and 384-bit or 640-bit accumulators for the step totals.
- **Merging.** Nearby reset states merge fast, so the orbit near any B can be found with no history: start every reset state in a window and advance the lowest. This produced the candidate first, then the 711 cut points that split the traversal into 712 segments. Every cut point is only a proposal: a segment must land exactly on the next segment's start.
- **Traversal.** `code/seg.c` ran all 712 segments, 5366672799056 phases in about 339 core-hours, on a desktop, a small cloud machine and two 32-core AWS machines. It adds raw steps per application, in telescoped form: 6·steps = 2(a_end² − a_start²) + Σ 6R. AWS reclaimed the first box at 20:37Z on Nov 3. Results were pulled every 2 minutes, the run resumed from checkpoints on the second box, and the chain check passes across the handoff.

## The Lean bridge

`code/lean/AMapBridge.lean` compiles against google-deepmind/cryptids commit c86f158 with no `sorry`, using only `propext`, `Classical.choice` and `Quot.sound` (`certs/lean_bridge_check.log`).

**What it proves.** The file defines the A-map `aNext` and proves `isHalt_of_aMap : (∃ N, aIter N (6,1) = none) → IsHalt target`. One step of the certified `highLevelNext` is 0, 1 or 2 A-map applications, under J(0,w) = A(6,w+1) and J(u,w) = A(2u,w+4) for u ≥ 1. The cryptids theorem `isHalt_iff_highLevel_acceleration` then carries this to the raw machine. So every map rule the halt relies on, in every case, is checked against the machine by the kernel, not just on finite ranges.

**What it does not prove.**
- That N exists. The orbit was computed in C, and N ≈ 6.7×10^26 has not been run in Lean. `IsHalt target` is therefore not a Lean theorem yet.
- Any step or ones count. Those formulas rest on the finite raw-machine checks below.
- The jump lemma. It is a hand argument, written at the top of `code/core.h`.

I rebuilt only this machine's module and its dependencies, and did not run the repo's own `verify.py` or comparator. `aNext` uses natural subtraction; a Python copy of it matches the run map with 0 differences on even a < 1500, b < 3100.

## Gates and checks

All of these passed with 0 failures. Logs are in `logs/` and `certs/`.

| Check | Result |
|---|---|
| Map and step polynomials against the raw TM | 70,800-case grid (even a ≤ 240, b ≤ 600) plus 3,000 random cases; every rule branch hit in the grid |
| Raw TM from blank, no acceleration | every one of 4,830 applications lands exactly on the predicted tape at the predicted step, through raw step 29,998,749,277 |
| Community near miss | A(2396758,2396763) at application 1,241,263, brute force in C and Python |
| Scout near miss | A(7516192762,7516192766) at application 4,312,829,551, brute force in C and Python |
| Jumping engine against brute force | 34,315 checkpoints; closest-approach tables identical on the 27 scales compared (10 to 36) |
| Step totals against per-rule sums | exact at B ≈ 2^33 (`brute_steps`, a plain C loop over the polynomials) |
| Whole prefix to B = 140737488355534 (about 2^47) | `seg` and `seg2.py` G agree on applications 41339082483821 and steps 2739392771739223374935112719918973553857; the Lean map reaches the same end |
| Whole prefix to B ≈ 2^67 | `orbit.c` (no step counts, no shared stretch reuse) visits (6,84326670788528159245) at application 25862939968802154961, same as the chain |
| A-map against Lean map | 319,997-case grid, 200,000 random cases up to 2^4000, first 3,000,000 steps of the orbit |
| Second implementation on samples | one stretch in each of the 712 segments (B from 2^59 to 2^91), plus 562 random stretches: applications and steps equal, Lean map reaches the same end |
| Accounting at a halt | 21 starts, including the corpus case A(6,35) → A(186,189): `seg` steps and ones equal the raw TM exactly |
| Final tape closed form | every even a in 6..798 |
| Final stretch | both implementations, from the merged state to the halt: applications and steps agree once the one-letter difference below is included |
| Window before the halt | all 8192 reset states with B in a 4096-wide window below the halt merge and then halt (independent Python); the Lean map also halts from the merged state |
| Chain | 712 of 712 segments link exactly from A(6,1); no failed link and no never-resetting tail |

The G form of the map stops one letter after A(a,a+3), at A(2a+6,0), which costs a²+3a+15 steps; another 4a+26 steps reach the halt. That equals a²+7a+41 exactly, as `logs/final_stretch_compare.txt` shows.

## What is confirmed and what is not

- **Machine-checked:** the map rules, through the Lean bridge.
- **Confirmed by two implementations:** the state, applications and steps on the whole prefix to about 2^47, and on sampled stretches above it; the end state under the Lean map on all of those; the final stretch to the halt.
- **Not independently confirmed:** the full totals. The final application and step counts come from `seg` alone. The second implementation covers only 147,324,928 of 5,366,672,799,056 phases above the prefix. It is far too slow in Python for a full run.
- **A limit of the chain check:** merging cuts both ways. A wrong jump in `seg` would probably rejoin the true orbit before the next cut point, so an exact link does not rule out a wrong total in that segment. The same merging makes the halt itself much less sensitive to such an error than the exact counts are.
- **Finite checks only:** the raw-step polynomials and the ones formula are verified on the cases above, not proved symbolically.
- **Same-code note:** `orbit.c` and `seg.c` share the guard logic in `core.h`, so `orbit.c` is a separate traversal loop, not a fully independent implementation.

A full second run would settle the totals. A fast independent engine, using a different form of the map and per-rule cost sums, is still to be written. `orbit.c` runs at about 1.4M phases/s, so a comparable engine would need roughly 1,000 core-hours, about 33 hours on 32 cores.

## Closest approaches and congruences

No congruence forbids the halt, since it happens. I did not prove any congruence. In all 308,669 sampled reset states, a0 = 6 goes with B ≡ 1 mod 4 and a0 = 22 with B ≡ 2 mod 4, and the halting state is in the second class. This is an observation, and the early orbit has at least one exception (a0 = 6, B ≡ 3 mod 4).

Near misses with |b−a−3| ≤ 1, plus the community's d = 2 (b−a−3 = +d or −d). Only the d = 2 entry and the halt form are in the corpus. The +1 at application 4312829551 is from this project's scout, and the rest are from this run:

| d | Application | a | b |
|---|---|---|---|
| +2 | 1241263 | 2396758 | 2396763 |
| +1 | 4312829551 | 7516192762 | 7516192766 |
| +1 | 1010625204869613 | 1688849860263930 | 1688849860263934 |
| −1 | 17129710022346449710 | 27670116110564327418 | 27670116110564327420 |
| +1 | 19942838493587156332 | 32281802128991715322 | 32281802128991715326 |
| 0 | 674564771793355691986675473 | 1083197534374707740536733690 | 1083197534374707740536733693 |

Closest approach per doubling, where scale is the bit length of the sweep's B. Applications and a, b for each are in `certs/closest_per_scale.tsv`.

| Scale | Phases | Closest +d | Closest −d |
|---|---|---|---|
| 20 | 3 | 65 | 33 |
| 21 | 220 | 8 | 120 |
| 22 | 5 | 11 | 51 |
| 23 | 295 | 2 | 160 |
| 24 | 3 | 129 | 15 |
| 25 | 773 | 164 | 15 |
| 26 | 6 | 37 | 5 |
| 27 | 1075 | 36 | 124 |
| 28 | 4 | 75 | 31 |
| 29 | 2811 | 108 | 35 |
| 30 | 5 | 61 | 9 |
| 31 | 3941 | 7 | 48 |
| 32 | 4 | 51 | 3 |
| 33 | 10218 | 218 | 48 |
| 34 | 6 | 1 | 89 |
| 35 | 14707 | 68 | 5 |
| 36 | 3 | 121 | 95 |
| 37 | 37735 | 8 | 22 |
| 38 | 5 | 27 | 85 |
| 39 | 56354 | 108 | 11 |
| 40 | 3 | 51 | 91 |
| 41 | 146483 | 18 | 8 |
| 42 | 5 | 59 | 55 |
| 43 | 215739 | 20 | 117 |
| 44 | 3 | 49 | 57 |
| 45 | 565069 | 24 | 191 |
| 46 | 5 | 43 | 71 |
| 47 | 819880 | 43 | 53 |
| 48 | 3 | 57 | 177 |
| 49 | 2145511 | 64 | 100 |
| 50 | 6 | 61 | 3 |
| 51 | 3108386 | 117 | 48 |
| 52 | 4 | 1 | 153 |
| 53 | 8194581 | 204 | 8 |
| 54 | 6 | 13 | 81 |
| 55 | 11539867 | 67 | 88 |
| 56 | 3 | 149 | 141 |
| 57 | 32016495 | 4 | 183 |
| 58 | 5 | 11 | 7 |
| 59 | 43578082 | 12 | 12 |
| 60 | 3 | 39 | 7 |
| 61 | 124769719 | 105 | 472 |
| 62 | 6 | 47 | 47 |
| 63 | 169918341 | 19 | 16 |
| 64 | 4 | 261 | 123 |
| 65 | 482960373 | 48 | 115 |
| 66 | 7 | 1 | 1 |
| 67 | 671796215 | 155 | 176 |
| 68 | 3 | 161 | 247 |
| 69 | 1859993666 | 9 | 21 |
| 70 | 5 | 61 | 41 |
| 71 | 2649928412 | 37 | 371 |
| 72 | 3 | 77 | 165 |
| 73 | 7190352837 | 132 | 142 |
| 74 | 6 | 133 | 69 |
| 75 | 10423479721 | 292 | 8 |
| 76 | 3 | 33 | 405 |
| 77 | 27810784067 | 211 | 192 |
| 78 | 5 | 37 | 75 |
| 79 | 40598684382 | 44 | 23 |
| 80 | 4 | 445 | 35 |
| 81 | 106751745276 | 61 | 412 |
| 82 | 5 | 33 | 209 |
| 83 | 157422594629 | 49 | 372 |
| 84 | 4 | 89 | 415 |
| 85 | 411692369173 | 301 | 160 |
| 86 | 5 | 107 | 51 |
| 87 | 613493039650 | 196 | 219 |
| 88 | 3 | 123 | 147 |
| 89 | 1600262100547 | 133 | 80 |
| 90 | 6 | 35 | 79 |
| 91 | 2384965823413 | 0 | 203 |

Even scales have few phases because the orbit crosses them in a handful of very long jumps. The table starts at scale 20; lower scales are in the file.

## Rerun and check

Requires gcc ≥ 14 (for `_BitInt`) and Python 3.

```sh
cd code
python3 check_chain.py ../certs/seglist.txt ../certs/segments     # seconds: chain, totals, closed form
./build_seg.sh                                                    # builds ./seg; train.txt holds the training stretch
./seg 6 1 6 6440847205 /tmp/g.txt; head -2 /tmp/g.txt             # want apps 1780810218, sum6R 2505855938148358542254952270
./replay_segment.sh 39                                            # rerun any segment, compare with the stored result
gcc -O2 -march=native -I. -w -o seg_x seg.c; python3 seg2.py G 6 1 6 6440847205   # second implementation
gcc -O2 -march=native -o raw_prefix raw_prefix.c; ./raw_prefix 30000000000        # raw TM from blank
gcc -O2 -march=native -o tm_check tm_check.c; ./tm_check grid 240 600             # map and step polynomials
python3 conj_check.py 400 200000 3000000                          # A-map against the Lean map
python3 halt_accounting_test.py; python3 halt_tape.py             # needs seg_x
sh ../certs/final_stretch_J.sh                                    # Lean map to the halt
```

A full replay is `./seg` over every line of `certs/seglist.txt`, about 339 core-hours. `check_chain.py` trusts the numbers `seg` wrote, so real checking means replaying segments.

Lean, with the repo's toolchain:
```sh
git clone https://github.com/google-deepmind/cryptids && cd cryptids && git checkout c86f158
lake exe cache get && lake build BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
lake env lean /path/to/code/lean/AMapBridge.lean
```

Stored: `certs/segments/` (one result per segment: start, end, applications, sum6R, closest approaches), `certs/seglist.txt`, `data/samples/` (reset states about every 2^24 phases, for replaying any stretch), and the cross-check logs. The `.log` files are in the evidence-logs-bb6 asset. `certs/xcheck_all_vacuous.log` holds 6 empty rows from a stretch-picking bug; those 6 segments were rerun and appear with real stretches in `certs/xcheck_all.log`. `data/seglist_v1.txt` is the list before oversized segments were split.

## Other caveats

- The corpus snapshot ends 2026-10-29 and the Lean repo was read on 2026-11-02, so someone may have found this independently since.
- `seg` was rebuilt during the run to add safe stopping and sampling. Every build used passed the same exact-prefix gate.

## Credit

This builds entirely on community and published work. Corpus paths are relative to `knowledge/` in the bbchallenge corpus.

- **Rule system, start and near miss:** Big_numbers (wiki) and a member, `discord/forum-individual-machines/threads/2026-10-01-1RB0LF_1RC1RA_0RD0RB_1LE-_0LA1LE_1RD1LA-1555316944914096188.md`.
- **Corrected map, its finite checks, the halting diagonal and the growing family L_n:** Dennis and a member, `discord/bb6/chat/2026-10-21--2026-10-26.md`.
- **Independent analysis and J form:** Marco Dos Santos, arXiv 2610.22603, with Gemini; **G(c,b) form:** a contributor to the wiki page. Both via `wiki/pages/Main/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA.wiki`.
- **Listing the machine as a potential Cryptid and asking for work on these machines:** Shawn Ligocki, `discord/bb6/chat/2026-10-21--2026-10-26.md`.
- **Lean formalization:** google-deepmind/cryptids, `BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean` at commit c86f158. It supplies the certified `highLevelNext`, the theorem the bridge relies on, and the hazard analysis in `Hardness.lean`.

Nothing here has been posted.
