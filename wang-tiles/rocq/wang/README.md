# BB_WT in Rocq: BB_WT(5) = 6, BB_WT(6) = 8, BB_WT(7) = 16, BB_WT(8) ≥ 17

This folder proves in Rocq (Coq 8.20.1, coq-native):

| Theorem | Statement (`WangTiles_Statement.v`) |
|---|---|
| `BB_WT_5` (`WangTiles_Theorem.v`) | `BB_WT_is 5 6`: some 5-tile set has score 6, and no 5-tile set has a larger score |
| `BB_WT_6` (`WangTiles_Theorem.v`) | `BB_WT_is 6 8` |
| `BB_WT_7` (`WangTiles_Theorem7.v`) | `BB_WT_is 7 16` |
| `BB_WT_8_lower` (`WangTiles_Theorem.v`) | `BB_WT_at_least 8 17`: some 8-tile set has score at least 17 |
| `plane_5`, `plane_6`, `plane_7` | every 5-tile set that tiles 7×7, every 6-tile set that tiles 9×9, and every 7-tile set that tiles 17×17 tiles the plane |

The definition is the wiki's and the BB_WT thread's: the score of a set of Wang tiles is the largest d such that it
tiles a d×d square, or 0 if there is no largest d, and BB_WT(n) is the maximum score over all n-tile sets. Colours
are natural numbers (unlimited), tiles are `[TOP,RIGHT,BOTTOM,LEFT]` and are not rotated or reflected, and an n-tile
set is a list of n distinct tiles. `WangTiles_Statement.v` holds these definitions and nothing else.

## Build

```sh
opam switch create rocq 4.14.2      # or any switch with OCaml 4.14.2
eval $(opam env)
opam install coq-native
opam pin add coq 8.20.1
tools/make_n7.sh ../../wang/certs/n7 8   # writes the n = 7 data files from the v1 certificate, 8 processes
make -j8
```

The n = 7 certificate is the release v1 download: 64 shards, 195 MB compressed (`wang/certs/n7/`). The Rocq data
files made from it are not kept here (775 MB of `.v`). `tools/make_n7.sh CERTDIR [PROCESSES]` regenerates them:

1. it checks the 64 shards against `CERTDIR/SHA256SUMS`;
2. `tools/c/recut.c` walks every shard as `wang/code/check_cert.c` does (so the v1 certificate is checked by C on the
   way; it keeps 128-bit fingerprints of the repeat-skip keys instead of the keys, to stay small) and writes each of the 5,519 subtrees at position 10 as its own token stream: the same tokens, with torus
   numbers changed to one shared table and with remember marks added (see below);
3. `tools/n7_assemble.py` shares the subtrees out over 72 jobs, the largest first, each to the least loaded job;
4. `tools/n7_to_coq.py` writes the Rocq files: the reference list of prefixes with each one's job
   (`n7/Wang7_Prefixes.v`), the shared torus table (`n7/Tori7*.v`), each job's Huffman-coded token stream
   (`n7/Job7_jJJJ_*.v`), its check (`n7/Check7_jJJJ.v`) and the list of jobs (`n7/Jobs7.v`), and `_CoqProject`;
5. it compares the generated files with `n7/MANIFEST.sha256`.

Everything is derived from the v1 certificate bytes by these tools; no new download and no search is needed. It
needs Python 3, xz and a C compiler, and takes 43 core-minutes, 239 s on 19 processes, at most 2.5 GB per process.
With `CHECK=1` it also checks every job with `tools/c/check4.c`, a C checker for the new format (37 more
core-minutes). `make small` builds n = 5, 6 and 8
alone (`WangTiles_Theorem.v` and what it needs), without the n = 7 data.

### Build time and memory

A clean build (`tools/make_n7.sh CERTDIR 19`, then `make TIMED=1 -j20`, from a fresh copy) took **4,336 s
(72 minutes)** of wall time on 20 cores of an AMD EPYC 9R14 shared with other work: 502 s to regenerate the n = 7
data, 3,834 s for `make` (`logs/build_clean.log`; `tools/summarize_build.py` makes this table from it). `recut` has
since been made single-pass: regenerating the same files now takes 239 s, so the same build would take about
4,070 s.

| Files | Count | Time each (s) | Peak memory |
|---|---|---|---|
| job 0 check (the largest subtree, 302.9M nodes) | 1 | 3,349 | 2.37 GB |
| job 1 check (the second largest, 272.5M nodes) | 1 | 3,673 | 1.77 GB |
| other job checks (56.6M nodes each) | 70 | 550–1,012, median 624 | 1.0–2.04 GB, median 1.29 GB |
| job data files (`n7/Job7_*`) | 640 | 1–5 | 0.45 GB |
| torus table files | 23 | 1–4 | 0.44 GB |
| reference list, job list, `BB_WT_7` | 3 | 8, 4, 7 | 1.42 GB |
| `WangTiles_Theorem.v` (n = 5, 6 checks and the champions) | 1 | 721 | 3.32 GB |
| all other files | 12 | 1–16 | 1.47 GB |
| `tools/make_n7.sh` (64 runs of `recut`, then the generators) | | 239 wall, 43 core-minutes | 2.5 GB |

The Rocq files take 15.3 core-hours in all, the job checks 14.4 of them; with the regeneration, 16.0. The two jobs with one large subtree each
set the critical path at about an hour; every other job takes under 17 minutes on a loaded core (546 s when the box
was quiet). On an 8-core desktop the build should take about two hours: `make -j8` keeps at most two of the large
jobs and six normal ones running, typically about 12 GB and at most about 16 GB (use `-j6` on 16 GB). `make small` (n = 5, 6
and 8, no n = 7 data) takes about 12 minutes on one core and 3.3 GB.

Against the part-1 build of the same proof (5,151 s on 20 cores, 16.5 core-hours, jobs up to 9.8 GB and the final
file at 10.7 GB, `logs/build_clean_part1.log`): the largest job is now 3.3 GB (the n = 6 check, unchanged) and the
largest n = 7 job 2.4 GB, the final file 1.4 GB, the longest job 61 minutes instead of 81, and the data 775 MB of
`.v` instead of 1.1 GB.

## Axioms

`Print Assumptions` (at the end of each theorem file) shows, for `BB_WT_8_lower`:

```
Closed under the global context
```

and for `BB_WT_5`, `BB_WT_6`, `BB_WT_7` and `plane_5` to `plane_7` only Rocq's primitive 63-bit integers and
primitive arrays:

```
PrimInt63.int, PrimInt63.{add, sub, mul, land, lor, lxor, lsl, lsr, eqb, ltb, leb},
PArray.array, PArray.{make, get, set}
```

These are the kernel's built-in types and operations (Rocq lists every primitive under "Axioms"). None of the
axioms that describe their behaviour (`Uint63.*_spec`, `eqb_correct`, `PArray.get_set_same`, ...) is used, so the
proofs hold whatever these operations compute: they are used only to load the certificate bytes, to hold the torus
table, and as caches whose answers are always re-checked. They matter only when the kernel evaluates the checker
on the stored certificate, which is where any proof by computation trusts the kernel and, with `native_compute`,
the OCaml compiler. No other axiom is used, not even functional extensionality.

## How the proof works

**Lower bounds** (`Wang_Refute.v`, `Wang_Champions.v`). For each champion: an explicit tiling of the d×d square,
checked edge by edge (`check_tiling`), and a search proved sound that shows no (d+1)×(d+1) tiling exists
(`refutes`). The search keeps a set of possible labels per cell, removes labels that no neighbour allows (arc
consistency with a worklist), and branches on the first undecided cell in centre-out order. The champions are the
wiki's for n = 5 and 6 and the sets in `wang/certs/champions/n7_d16.*` and `n8_d17.*`.

**Upper bounds** (`Wang_Checker.v`, `Wang_Sound.v`, `Wang_Upper.v`). `check` walks the same tree as
`wang/code/check_cert.py` and reads the same tokens as the existing certificates (`wang/certs/upper/n5_D7_ringsym`,
`n6_D9_ringsym`, and the 64 shards of `wang/certs/n7/n7_D17`, regrouped into 72 jobs as above; the SHA-256 of each
source file is in the header of the generated data file). It fills the D×D square cell by cell in ring order with labels named by first appearance
and keeps the colour equalities that adjacency forces, as two relations between labels. At each node the
certificate either names a torus, which the relations must imply, or claims the relations closed, or says nothing.
The checker skips a node when a rotated or reflected image reads smaller (symmetric skip) or when an earlier node
had the same state up to a renaming of labels (repeat skip). A complete fill with nothing settled fails the check.

- *Closed claims* (n = 7). The relations admit no D×D square, which the refutation search above shows with the
  relations as the adjacency rule, and every relation one colour merge larger is settled, by a torus or by being
  closed itself. A tile set satisfying the relations either has exactly them, and then tiles no D×D square, or
  satisfies one more merge (`closed_sem`). Verified closed relations are kept in a set of their own, compared
  structurally, so the proof never relies on the caches.
- *The visit gate* (n = 7) only decides when the certificate gives a second token for a relation pair; every
  token is checked like any other.
- *Jobs* (n = 7). The tree is cut at position 10: there are 5,519 nodes there. The reference list
  (`n7/Wang7_Prefixes.v`) gives, for each of them in walk order, the labels of cells 0 to 9 and the one job that
  walks it (`owners7`); every job walks the part above position 10 and, at the i-th node there, walks the subtree
  only if `nth i owners7 0` is its own number. Every job records the labels of cells 0 to 9 at each of these nodes,
  and the check requires that list to equal the reference list exactly, element by element; no digest is used.
  `labels_sound` then combines the jobs: a labelling's path through job 0 either ends in a plane tiling or reaches a
  node with index i that job 0 leaves, and job `nth i owners7 0` walks that node, because both recorded the same list
  and a prefix occurs in it only once (`refs7_nodup`, checked by computation). `certs7_ok` checks that each of the 72
  jobs passes, that every job number below 72 has its certificate, and that every owner is below 72
  (`owners7_bound`), so every node at position 10 is walked by exactly one job.
- *Remember marks* (n = 7). Below position 10 the checker stores a repeat-skip key only where the certificate's
  marks say so: a mark gives the number of keys not found in the table until the next one to store. `recut` puts a
  mark on exactly the keys that are hit again later in the subtree, about 4% of them, which keeps the table small.
  Storing fewer keys only means fewer skips: a wrong or missing mark can make the walk longer or make it read the
  certificate out of step and fail, but never makes a check pass that should fail (`mark_step_same`: a mark step
  changes no part of the state the proof depends on).

`walk_root` proves, for one job: every valid full labelling of the square, for any tile set, either comes with a
plane tiling of that set or has its prefix deferred to another job. The proof is by strong induction on the
labelling read as a number. Follow its path down the tree. A torus leaf gives a periodic plane tiling. A closed
leaf gives one by `closed_sem`. A symmetric skip gives a smaller labelling of the rotated set, which tiles the plane
exactly when the original does. A repeat skip gives a smaller labelling of a renamed set, by gluing the rest of the
labelling onto the earlier node. `plane_from_certs` turns this into the statement about lists of tiles, and
`score_upper` into the bound on scores.

What the proof does not rely on: the certificate data, the torus table, the caches, the remember marks, the job
list and the reference prefix list. Every claim is re-checked against the relations at the node where it is used,
every repeat-skip key is decoded and compared with the current state as a structure, and a certificate or list that
does not fit makes the check fail. How the data are stored is free for the same reason: the token streams are
Huffman coded (one code per job), 62 bits per integer, and the tori are packed 3 bits per cell, all in arrays of
2^16 integers; only `Wang_Checker.v` decodes them.

## Files

| File | Contents |
|---|---|
| `WangTiles_Statement.v` | tiles, square and plane tilings, score, BB_WT |
| `Wang_Rel.v` | relations between labels, colour merges and their lemmas |
| `Wang_Refute.v` | the refutation search on any adjacency relations, proved sound |
| `Wang_Checker.v` | the certificate checker (computation only) |
| `Wang_Geom.v` | label tilings, symmetries of the square and the plane, tori give plane tilings |
| `Wang_Canon.v` | naming labels by first appearance, the lexicographic order |
| `Wang_Sound.v` | closed claims (`closed_sem`) and the walk (`walk_root`) |
| `Wang_Upper.v` | jobs combined, and from labellings to tile sets (`labels_sound`, `plane_from_certs`, `score_upper`) |
| `Wang_Champions.v` | explicit tilings and refutations for tile sets |
| `WangTiles_Theorem.v`, `WangTiles_Theorem7.v` | the theorems and `Print Assumptions` |
| `Wang_Champions_Data.v`, `Cert_n5_D7.v`, `Cert_n6_D9.v` | data, generated by `tools/` from `wang/certs/` |
| `n7/*.v` (generated by `tools/make_n7.sh`), `n7/MANIFEST.sha256` | the n = 7 reference list, torus table, job data, job checks and job list; the hashes of the generated files |
| `tools/make_n7.sh`, `tools/c/recut.c`, `tools/n7_*.py`, `tools/wtcoq.py` | the n = 7 data from the v1 certificate |
| `tools/c/check4.c` | a C checker for the jobs, the same rules as `Wang_Checker.v` |
| `tools/cert_to_coq.py`, `tools/champions_to_coq.py` | the n = 5, 6 data and the champions |
| `logs/` | build logs and the measurements cited in `ROCQ.md` |

## Credits

The problem, the definition and the n = 5 and 6 champions are from the BB_WT thread and the bbchallenge wiki's
Wang Tiles page (see `wang/RESULT.md` for the full credits). The certificates, the n = 7 and 8 champions and the
tree method are from `wang/`. The build layout follows Coq-BB5 (ccz181078/Coq-BB5, MIT); no code from it is used.
