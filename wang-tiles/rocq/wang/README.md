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
tools/make_n7.sh ../../wang/certs/n7  # writes the n = 7 data files, see below
make -j20
```

The n = 7 certificate is 64 shards, 195 MB compressed (`wang/certs/n7/`). Its data files are not kept here (1.1 GB of
`.v`). `tools/make_n7.sh CERTDIR` checks the shards against `CERTDIR/SHA256SUMS`, writes `n7/Cert7_sNNN.v` (the
shard's bytes and tori as Rocq data) and `n7/Check7_sNNN.v` (the lemma that the shard passes), and compares what it
wrote with `n7/MANIFEST.sha256`. It needs Python 3 and takes a few seconds. `make small` builds everything except
n = 7 (`WangTiles_Theorem.v` and what it needs) without the n = 7 data.

### Build time and memory

A clean build (`tools/make_n7.sh` then `make TIMED=1 -j20`, from an empty directory) took **5,151 s (86 minutes)** of
wall time on 20 cores of an AMD EPYC 9R14 (`logs/build_clean.log`), 59,300 core-seconds (16.5 core-hours) in all:

| Job | Count | Time each | Peak memory each |
|---|---|---|---|
| `n7/Check7_sNNN.v`: one shard's check, under `native_compute` | 64 | 423–4,874 s, median 705 s, 55,408 s in all | 2.0–9.8 GB |
| `n7/Cert7_sNNN.v`: one shard's data | 64 | 39–82 s | 1.6–2.6 GB |
| `WangTiles_Theorem7.v`: combining the shards, `refs7_nodup` (24 s), `BB_WT_7` | 1 | 81 s | 10.7 GB (it loads all 64 shards) |
| `n7/Certs7.v`, `n7/Checks7.v` | 2 | 9 s | 5.8 GB |
| `WangTiles_Theorem.v`: n = 5, 6 checks and the champions | 1 | 695 s | 3.1 GB |
| all other files | 14 | under 20 s each | at most 1.1 GB |

The critical path is shard 0 (410M nodes, 4,874 s); shard 2 (328M nodes) takes 4,535 s and every other shard under
1,700 s. More cores do not help past that. With 20 jobs the box had about 50 GB in use, other lanes' work included. `make small` (n = 5, 6
and 8, no n = 7 data) takes about 12 minutes on one core (its files sum to 724 s in the clean build) and 3.1 GB.

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
`wang/code/check_cert.py` and reads the existing certificates byte for byte (`wang/certs/upper/n5_D7_ringsym`,
`n6_D9_ringsym`, and the 64 shards of `wang/certs/n7/n7_D17`; the SHA-256 of each source file is in the header of
the generated data file). It fills the D×D square cell by cell in ring order with labels named by first appearance
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
- *Shards* (n = 7). The tree is cut at position 10: there are 5,519 nodes there, and shard s walks those whose
  index is s modulo 64. Every shard also records the labels of cells 0 to 9 at each of these nodes, in order, and
  the check requires that list to equal one reference list (`n7/Wang7_Prefixes.v`) exactly, element by element.
  `labels_sound` then combines the shards: a labelling's path through shard 0 either ends in a plane tiling or
  reaches a node shard 0 leaves to shard t, and shard t walks that node, because both recorded the same list and a
  prefix occurs in it only once (`refs7_nodup`, checked by computation).

`walk_root` proves, for one shard: every valid full labelling of the square, for any tile set, either comes with a
plane tiling of that set or has its prefix deferred to another shard. The proof is by strong induction on the
labelling read as a number. Follow its path down the tree. A torus leaf gives a periodic plane tiling. A closed
leaf gives one by `closed_sem`. A symmetric skip gives a smaller labelling of the rotated set, which tiles the plane
exactly when the original does. A repeat skip gives a smaller labelling of a renamed set, by gluing the rest of the
labelling onto the earlier node. `plane_from_certs` turns this into the statement about lists of tiles, and
`score_upper` into the bound on scores.

What the proof does not rely on: the certificate data, the torus table, the caches and the reference prefix list.
Every claim is re-checked against the relations at the node where it is used, every repeat-skip key is decoded and
compared with the current state as a structure, and a certificate or list that does not fit makes the check fail.

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
| `Wang_Upper.v` | shards combined, and from labellings to tile sets (`labels_sound`, `plane_from_certs`, `score_upper`) |
| `Wang_Champions.v` | explicit tilings and refutations for tile sets |
| `WangTiles_Theorem.v`, `WangTiles_Theorem7.v` | the theorems and `Print Assumptions` |
| `Wang_Champions_Data.v`, `Cert_n5_D7.v`, `Cert_n6_D9.v` | data, generated by `tools/` from `wang/certs/` |
| `n7/Wang7_Prefixes.v`, `n7/Certs7.v`, `n7/Checks7.v`, `n7/MANIFEST.sha256` | the n = 7 reference prefixes, the shard list, and the hashes of the generated files |
| `tools/` | the data generators; `tools/c/prefixes.c` regenerates the prefix list from a shard |

## Credits

The problem, the definition and the n = 5 and 6 champions are from the BB_WT thread and the bbchallenge wiki's
Wang Tiles page (see `wang/RESULT.md` for the full credits). The certificates, the n = 7 and 8 champions and the
tree method are from `wang/`. The build layout follows Coq-BB5 (ccz181078/Coq-BB5, MIT); no code from it is used.
