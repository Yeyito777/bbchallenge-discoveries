# BB_WT: exact values for n = 5, 6 and 7, and a new bound for n = 8

> Written before the Rocq proof, so "What is certified" and "Open caveats" describe the state without it. For the proof, see `../rocq/wang/ROCQ.md`. Host names were replaced when staging.

## Claim

BB_WT(5) = 6, BB_WT(6) = 8 and BB_WT(7) = 16. The first two turn the wiki's lower bounds into exact values. The third
replaces the wiki's BB_WT(7) ≥ 11 with an exact value from a new champion:
`[4,0,3,0] [3,0,4,1] [3,1,3,2] [5,2,4,0] [4,1,4,2] [4,1,3,1] [3,2,5,0]` tiles a 16×16 square and refuses 17×17, and
every 7-tile set that tiles 17×17 tiles the plane. BB_WT(3) = 3 and BB_WT(4) = 4 are independently reproduced. Also,
BB_WT(8) ≥ 17, against the wiki's ≥ 14, from the same 7 tiles plus `[0,0,3,1]`, using all 8 tiles.

**How strong each claim is.** For n = 3 to 6, two separate brute-force searches (A and C) agree on the whole score
histogram, a third method (B) agrees on the value and the top-scoring sets, and B's certificates pass both checkers.
n = 7 is weaker on one point: one search (B), with its certificate passing the C checker on all 64 shards and the
Python checker on 4 shards, and no complete second search. See "n = 7".

## Definitions used

From the wiki page and the thread, with no change:

> Define the *score* of a set of Wang tiles as the largest d such that it can tile a d×d square, or 0 if there
> is no largest d. Then BB_WT(n) = the maximum score over all n-tile sets.

Sources: `knowledge/wiki/pages/Main/Wang_Tiles.wiki` (revid 8879), and in
`knowledge/discord/forum-general/threads/2026-07-22-BB_WT-Busy-Beaver-function-for-Wang-Tiles-1529586687926210691.md`
the records "BB_WT(n) definition", which adds that colours are unlimited and there is no seed tile or other
constraint, and "Score 0 ⇔ the set tiles the whole plane". Tiles are written `[TOP,RIGHT,BOTTOM,LEFT]` as on the
wiki. They may not be rotated or reflected.

### The 8-tile bounds and padding

Neither source requires an n-tile set to use every tile in its tilings. There are two 8-tile certificates, and the
second does not depend on that question.

**Padding, BB_WT(8) ≥ 16.** Add `[6,7,8,9]`, whose four colours are pairwise different and appear on no other tile.

- It is a new tile, so the set has 8 distinct tiles.
- Its right colour 7 differs from every left colour, including its own 9, and the same holds on the other three
  sides. So it cannot touch any tile, itself included. It can appear only in a 1×1 square, and never in a larger
  square or in a plane tiling.
- So for d ≥ 2 the padded set tiles d×d exactly when the 7-tile set does, and its score is also 16.

`certs/champions/n8_d16_padded.*` holds this set with its own 16×16 tiling and 17×17 UNSAT proofs. Its stored tiling
uses only tiles 0 to 6.

**A real 8-tile set, BB_WT(8) ≥ 17.** `code/extend_one_tile.py` tried adding one tile to the 7-tile champion and found
`[4,0,3,0] [3,0,4,1] [3,1,3,2] [5,2,4,0] [4,1,4,2] [4,1,3,1] [3,2,5,0] [0,0,3,1]`, which tiles 17×17 and refuses 18×18.
`certs/champions/n8_d17.*` holds its tiling, which uses all 8 tiles, and its UNSAT proofs. So the bound does not
depend on padding or on how "n-tile set" is read. Five other one-tile additions also score 17, and none found scored
higher (`logs/extend_n8_partial_before_reboot.log`).

That scan covered only the first 38 or so of 2,720 candidate tiles. It was stopped by a planned reboot of the machine after
about 2.5 hours. A rerun was also stopped, because at that speed the full scan would take about a week. A higher score
may exist among the rest, and none of this says anything about the exact value of BB_WT(8).

## Exact numbers

Labelled pairs (H,V), where H = {(i,j): right of i matches left of j} and V = {(i,j): bottom of i matches top of
j}. Each is a disjoint union of bicliques, so the totals are the squares of the relation counts. All three runs
produced these numbers identically (`logs/hist_*`):

| n | relations | pairs | plane | score 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 3 | 128 | 16,384 | 6,037 | 7,203 | 3,084 | 60 | | | | | |
| 4 | 2,100 | 4,410,000 | 1,590,099 | 1,374,493 | 1,396,040 | 48,456 | 912 | | | | |
| 5 | 48,032 | 2,307,073,024 | 791,848,501 | 506,479,323 | 955,500,180 | 51,507,180 | 1,704,240 | 31,920 | 1,680 | | |
| 6 | 1,444,212 | 2,085,748,300,944 | 675,525,947,811 | 322,236,977,365 | 1,012,211,419,568 | 72,667,838,520 | 3,006,458,160 | 95,174,640 | 4,179,600 | 262,080 | 43,200 |

Unresolved pairs: 0 for every n.

Champions up to tile relabelling and the 8 symmetries of the square, in `data/champions_n{3,4,5,6}.txt`:

| n | value | classes at the top score | minimal classes | wiki champion among them |
|---|---|---|---|---|
| 3 | 3 | 4 | 1 | yes |
| 4 | 4 | 14 | 4 | yes |
| 5 | 6 | 4 | 4 | yes |
| 6 | 8 | 13 | 13 | yes |

## Method

Colours matter only through H and V, so an n-tile set is a pair of relations. Every set is in exactly one of two
finite states when n ≤ 10: it tiles a torus, or it refuses some finite square. Both are finite to check, and
Jeandel–Rao's "no aperiodic set with ≤ 10 tiles" (arXiv 1506.06492, as cited in the thread) is why the search can
be expected to end, but no result here depends on it, because every plane tiling claimed is an explicit torus.

- **A: `code/wt_pairs.c`.** Brute force over all pairs, in two symmetry modes that must agree. Exact DFS with an
  exact-key failure memo for squares; rectangular DFS and a width-b row-cylinder test for tori, and every torus
  found is verified. At n = 6 mode 0 ran 5,184,721,080 pairs and mode 1 ran 722,707,291.
- **C: `code/wt_csp.rs`.** A separate cross-check of the full histogram. Relations come from walking all colourings
  and deduplicating, classes from union-find, and squares and lattice tori from arc consistency with branching.
  724,678,576 pairs at n = 6.
- **B: `code/wt_lazy.rs`.** Never enumerates tile sets. It fills a D×D square cell by cell with abstract labels and
  merges colours only when an adjacency forces it. A node whose forced equalities already admit a torus is a leaf.
  With no holdout at D, every n-tile set tiling D×D tiles the plane, so BB_WT(n) < D.
- **Checkers: `code/check_cert.py` (standard library only) and `code/check_cert.c`.** They walk B's tree themselves
  and read only B's claims: which torus settles a pair, or that a pair is closed. All skip decisions are made
  by the checker. The proof is in the header of `check_cert.py`.

## Gates reproduced

| Gate | Result | Log |
|---|---|---|
| Relation counts 128, 2,100, 48,032, 1,444,212 for n = 3..6 | Exact, from raw colourings (Bell(2n) walks) and from the closed form Σ k!·S(n+1,k+1)² | `logs/gate_counts.log` |
| BB_WT(3) = 3, BB_WT(4) = 4 | Exact, A, C and B agree | `logs/hist_*`, `logs/compare_all.log` |
| Wiki champions n = 1..9 at their listed scores | Each tiles d×d and refuses (d+1)×(d+1), by arc-consistency search and by CaDiCaL | `logs/gate_champions.log`, `logs/sat_wiki.log` |

n = 10 (≥ 212) has no colouring on the wiki, so it was not checked.

## What is certified

**Upper bounds, `certs/upper/`.** n1_D2, n2_D3, n3_D4, n4_D5, n5_D7 and n6_D9, each in two orders: `ringsym` (with
the symmetry skip) and `shell` (no symmetry). All pass both checkers, except that the n = 6 `shell` tree is checked
by C only.

| Certificate | Nodes | Leaves | Tori | Tree bytes | Checked by |
|---|---|---|---|---|---|
| n5_D7_ringsym | 289,369 | 229,449 | 1,127 | 59,738 | C, Python |
| n5_D7_shell | 868,387 | 688,191 | 3,015 | 241,642 | C, Python |
| n6_D9_ringsym | 69,208,331 | 56,205,975 | 17,670 | 2,713,422 | C, Python |
| n6_D9_shell | 125,578,622 | 102,621,930 | 62,229 | 12,730,610 | C |

Python's run on n6_D9_ringsym matched C's counts exactly (`logs/check_py_n6_D9_ringsym_final.log`). Regenerating all
twelve certificates with the final build gave byte-identical files (`logs/regen_compare.log`).

**Mutation tests (`logs/mutation.log`).** `code/mutation_test.py` made 600 random changes to two good certificates: a
tree byte, a torus cell or a truncation. Both checkers gave the same verdict on every mutant, and rejected all
torus-cell and truncation mutants. 7 of 225 tree-byte mutants were accepted. The test does not examine them one by
one. They passed the same checks as any certificate, so each must still prove its claim, most likely with a
different torus that is also implied. Certificates one size too small (n = 5 at D = 6, n = 4 at D = 4, n = 6 at D = 8)
are rejected as "complete fill with no torus".

**Champions, `certs/champions/`.** For each of n7_d16, n8_d17, n8_d16_padded, wiki_n5_d6 and wiki_n6_d8:

- `.tiles`: the set.
- `.dD.tiling`: an explicit D×D tiling, checked edge by edge.
- `.d(D+1).cnf`: regenerated from the tile list and compared byte for byte.
- `.drat` and `.lrat`: CaDiCaL 3.0.1 UNSAT proofs (tool commits in `logs/tool_versions.log`).

drat-trim reports `s VERIFIED` and the formally verified cake_lpr reports `s VERIFIED UNSAT` on all five
(`logs/check_proofs.log`). The n = 7 16×16 tiling uses all 7 tiles.

**A against B at the top level.** Every B holdout at D = BB is one of A's top classes, every A class lies above a
B holdout, the labelled counts equal the orbit sizes, and each class is rescored from an explicit colouring
(`logs/compare_all.log`).

## n = 7

**Lower bound.** The set above, in `certs/champions/n7_d16.*`. B found it as a holdout while sampling a D = 12 run.

**Upper bound.** `certs/n7/` holds B's run at D = 17 with `ringsym`, split into 64 shards (subtree reset at position
10, visit gate 500), 195 MB compressed.

| | |
|---|---|
| Holdouts | 0 in all 64 shards |
| C checker, from the compressed files | 64 of 64 pass (`logs/check_c_n7_from_xz.log`) |
| Nodes walked, total | 4,537,499,086 |
| Leaves, total | 3,849,639,492 |
| Pairs checked as closed, total | 77,703 |
| Subtrees at position 10 | 5,519, with the same digest in every shard, so the shards share out one list |
| Python checker, 4 of 64 shards | Shards 1, 31, 54 and 60 pass, with nodes, leaves, tori, subtrees and digest matching C (`logs/check_py_n7_s*.log`) |

So every 7-tile set that tiles 17×17 tiles the plane, and BB_WT(7) = 16.

**Python on all 64 shards was not run.** Shard 1 (57,111,261 nodes) took 40 CPU minutes on a Ryzen 5 3600XT desktop, so all 4,537,499,086
nodes would take about 53 core-hours, which is past the "few hours" limit on the cores available. The 4 shards checked
hold 168,777,779 nodes, 3.7% of the total, and they are not a random sample: shards 31, 54 and 60 are three of the five
smallest. The heavier shards, such as shard 2 with 327,782,322 nodes, have been checked by C only.

**No complete second search at n = 7.** A brute-force run of A was stopped at 438 of 10,933 classes (11,920,942,509
pairs) to free cores for B. It is resumable (`wt_pairs 7 1 DIR WORKERS 10`) and needs about 30 more core-hours. Those
classes contain only scores up to 4, so it neither supports nor threatens the top of the range. For n = 7 the
evidence is the certificate and its checkers, not agreement between two searches. Finishing A would be the natural
next step for anyone wanting that, and it would also give the n = 7 histogram.

**Not known at n = 7.** How many sets reach 16. B's D = 16 holdout list, which would give all of them, was not run.

**Build provenance.** B got several speed changes during the run, and the shards came from three builds: three shards
from an early build and the rest from builds that added failed-search and refusal caches and a longer torus search at
the visit gate. These change which claims B makes and how fast, not what the checker accepts. Every shard is checked by
the same final checker. The final build reproduces shard 31 byte for byte.

**Certificate format changes during the work.** Python's first n = 6 pass (2026-11-02, format v2) is superseded by the
final pass on the final format and checker.

## How to rerun and check

```sh
cd code
python3 gate_counts.py 6
python3 gate_champions.py
gcc -O2 -o ../build/wt_pairs wt_pairs.c
gcc -O2 -o ../build/check_cert check_cert.c
rustc -O --edition 2021 -o ../build/wt_lazy wt_lazy.rs
rustc -O --edition 2021 -o ../build/wt_csp wt_csp.rs
cd ..

# check the stored upper-bound certificates: needs nothing but Python, or the C checker
python3 code/check_cert.py certs/upper/n5_D7_shell
build/check_cert certs/upper/n6_D9_ringsym

# check the n = 7 certificate: about 30 minutes on 2 cores, needs xz
code/check_shards.sh build/check_cert certs/n7 n7_D17 64 2

# check the champions: tiling, CNF and proofs
code/check_proofs.sh TOOLDIR certs/champions   # TOOLDIR holds drat/drat-trim and cake/cake_lpr

# regenerate an upper-bound certificate, then histograms
build/wt_lazy 6 9 ringsym 12 /tmp/n6_D9 -
build/wt_pairs 6 1 /tmp/a6 4 8 && python3 code/aggregate.py 6 /tmp/a6
build/wt_csp 6 /tmp/c6 4 && python3 code/aggregate.py 6 /tmp/c6

# regenerate the n = 7 certificate, one shard at a time
code/run_shards.sh build/wt_lazy 7 17 /tmp/run7 10 64 500 2 0 63

# independent SAT re-solve, and the one-tile scan, both need python-sat
python3 code/sat_check.py --wiki
python3 code/extend_one_tile.py "TILES" D MAXD
```

Python's run on n = 6 took under an hour on a loaded machine. C takes under a minute. `code/check_shards.sh` also
accepts uncompressed shards. Shards took 8 to 25 minutes each on that desktop, at nice 19.

## Open caveats

- n = 7 has no complete second search (see "n = 7"), so it does not meet the two-implementation standard the way
  n = 3 to 6 do. The upper bound rests on the certificate, the soundness argument in `check_cert.py`, and the C
  checker, with Python on a sample.
- Reading of "n-tile set". No source requires using every tile. The padded 16 bound relies on that, the 17 bound does
  not. The exact values for n = 5, 6 and 7 are attained by sets that use all their tiles.
- Duplicate tiles. A pair whose two tiles have identical colours is a set with fewer distinct tiles. Such pairs are
  counted in the histograms but cannot change a maximum, because padding gives the same score with distinct tiles.
- A, B and C were written by one author, with different methods and languages but the same understanding of the
  definitions. The stored certificates are what removes the need to trust the searches.
- The checkers themselves are trusted. They are short and were written to be read, and the two share a design, so a
  flaw in the soundness argument would affect both. The n = 7 argument adds two skips and closure on top of the
  plain tree walk, and it has not been reviewed by anyone else. The `shell` certificates for n ≤ 6 use no symmetry
  skip and no closure, as a simpler baseline.
- cake_lpr is formally verified, but the CNF encoding is mine: `champion_cert.py` regenerates it from the tile list,
  and the encoding is about 10 lines.
- BB_WT(8) ≥ 17 now equals the wiki's BB_WT(9) ≥ 17, so the wiki's n = 9 entry no longer adds anything over n = 8.
  Neither has been searched beyond the partial one-tile scan.

## Credit

The definition and the problem are from the BB_WT thread (corpus path above). Shawn Ligocki linked the earlier
discussions and gave the finiteness counterexample and the conjectured family BB_WT(n) ≥ 2n−4. member A gave the
definition, the score-0 argument, the hand proofs for n = 1 and 2, the construction BB_WT(n) ≥ n, the PTC program
behind BB_WT(3) = 3 and BB_WT(4) = 4, and the n = 5 champion, and asked for independent verification of 3 and 4.
Tracking the colouring rather than the connections, as B does, is PTC v2's idea, and B is otherwise a different
algorithm. Azerty and member D contributed the n = 9 bound and the Jeandel–Rao connection. The wiki's champions are
from the Wang Tiles page.
