# Wang tiles lane: what is proved in Rocq

## Proved

In Rocq 8.20.1 with coq-native, from the definitions in `WangTiles_Statement.v` (the wiki's and the BB_WT thread's,
quoted in `wang/RESULT.md`):

- `BB_WT_5 : BB_WT_is 5 6`, `BB_WT_6 : BB_WT_is 6 8` and `BB_WT_7 : BB_WT_is 7 16`: exact values.
- `BB_WT_8_lower : BB_WT_at_least 8 17`: lower bound (`BB_WT_7_lower` is also kept).
- `plane_5`, `plane_6`, `plane_7`: every 5-tile set that tiles 7×7, every 6-tile set that tiles 9×9, and every 7-tile
  set that tiles 17×17 tiles the plane.

Each lower bound is a champion with an explicit tiling and a proved-sound search refusing the next size. Each
upper bound runs one checker, proved sound in Rocq, on the existing certificate's tokens:
`wang/certs/upper/n5_D7_ringsym` (289,369 nodes), `n6_D9_ringsym` (69,208,331 nodes), and the 64 shards of
`wang/certs/n7/n7_D17` (4,537,499,086 nodes), regrouped into 72 jobs. The proof covers everything `check_cert.py`
does:
- the symmetric skip and the repeat skip;
- the torus-to-plane step;
- closed claims (77,703 in the n = 7 certificate), the visit gate, and the subtree resets at position 10;
- the step from tile lists to labels named by first appearance.

The job list is checked exactly. One reference list gives, for each of the 5,519 nodes at position 10 in walk
order, the labels of cells 0 to 9 and the one job that walks it. Each job's check compares the prefixes it recorded
with that list element by element, the list is shown duplicate-free by computation, every owner is shown to be
one of the 72 jobs, and every job number has its certificate (`certs7_ok`). No digest or hash is trusted. The upper
bounds hold for any list of n tiles, duplicates allowed, which is stronger than the statement needs.

## Build time and memory

A clean build, from regenerating the n = 7 data out of the v1 shards to `BB_WT_7`, took 4,336 s (72 minutes) on 20
cores of the shared AMD EPYC 9R14 box: 502 s for `tools/make_n7.sh`, 3,834 s for `make -j20`; 15.3 core-hours for
the Rocq files (`logs/build_clean.log`, per file). `recut` was then made single-pass; a second regeneration from
the v1 shards wrote the same 738 files (it matched `n7/MANIFEST.sha256`) in 239 s, 43 core-minutes. The table in
`README.md` gives each kind of job.

| | Part 1 (64 shards) | Now (72 jobs) |
|---|---|---|
| Wall time, 20 cores, clean | 5,151 s | 4,336 s (502 s of it regenerating the data) |
| Core-hours | 16.5 | 15.3 for the Rocq files, 16.0 with the regeneration |
| Largest job | 10.7 GB (`WangTiles_Theorem7.v`) | 3.3 GB (the n = 6 check); n = 7: 2.4 GB |
| Final n = 7 file | 90 s, 10.7 GB | 7 s, 1.4 GB |
| n = 7 checks | 64, 423–4,874 s, 2.0–9.8 GB | 70 of 550–1,012 s and 1.0–2.0 GB, two of 3,349 and 3,673 s |
| n = 7 data | 64 files, 3,246 s, 1.1 GB of `.v` | 663 files, 2,481 s, 775 MB of `.v` |
| Regenerating the data | a few seconds | 239 s wall on 19 processes, 43 core-minutes, at most 2.5 GB each |

Targets set for this change were every job at most about 4 GB (met: 3.3 GB), no job over about 20 minutes on one
core (met by all but jobs 0 and 1), and as few core-hours as possible (16.5 down to 15.3 for the Rocq files, 16.0
with the new regeneration step; the checks themselves barely changed, see Limits).

## Axioms

The lower bounds are closed. The upper bounds list only Rocq's primitive integers and arrays (the types and their
operations), the same list as before this change. No axiom about them is used, so the proofs do not depend on what
they compute; they carry the certificate data and caches whose answers are always re-checked. See `README.md`.

## How to check it

```sh
cd rocq/wang
tools/make_n7.sh ../../wang/certs/n7 8   # checks SHA256SUMS, rebuilds n7/*.v from the v1 shards, checks MANIFEST
make -j8                                 # needs coq 8.20.1 + coq-native, as Coq-BB5
make small                               # n = 5, 6, 8 only, no n = 7 data needed
```

The n = 7 data are derived from the v1 certificate bytes by the tools in `tools/`, with no search and no new
download; `tools/make_n7.sh` checks the shards against their `SHA256SUMS` first and compares everything it writes
(the 737 files of `n7/` and `_CoqProject`; a second regeneration on the box matched it) with `n7/MANIFEST.sha256`. What the tools change is how the same tokens
are grouped and stored:

- **Jobs instead of shards.** The 5,519 subtrees at position 10 are shared out over 72 jobs by node count, the two
  largest subtrees (302,926,221 and 272,526,920 nodes) alone in jobs 0 and 1, the rest 56.6M nodes each. Each
  subtree's tokens are the bytes of the v1 shard that walked it; the tokens above position 10 are the same in every
  shard and are copied into every job.
- **One torus table.** The 64 shards' tables are merged into one of 408,967 tori; each job builds only the tori it
  uses.
- **Remember marks.** Inside each subtree the checker stores only the repeat-skip keys that are hit again later,
  34.5M of the 650.7M keys the v1 walk stores below position 10. A mark only decides what is stored: a wrong or missing mark can make
  the walk longer, or make it read the certificate out of step and fail, but never makes a failing check pass.
- **Compact data.** Each job's token stream is Huffman coded (322.5M tokens in 34.8M integers, against 64M
  integers of plain bytes), the tori are packed 3 bits per cell, and all data are array literals of 2^16 integers.

## Tests beyond the build

- `tools/c/check4.c`, a C checker with the same rules as `Wang_Checker.v`, passes all 72 jobs (`CHECK=1
  tools/make_n7.sh ...`). `tools/c/recut.c` walks and checks every v1 shard as `check_cert.c` does while it writes
  the jobs (with 128-bit fingerprints of the repeat-skip keys; a collision would put its walk out of step with the
  shard and fail it).
- Three versions of `recut` (full keys and two passes, fingerprints and two passes, fingerprints and one pass) give
  byte-identical output; the last one is used (`logs/n7_v4_notes.txt`).
- The same Rocq checker passes the n = 3 and n = 4 certificates (`n3_D4_ringsym`, `n4_D5_ringsym`).
- It rejects four corrupted copies of the n = 5 certificate: three with one torus id changed, one cut in half.
- A first version of `recut` numbered the remember marks over all key lookups instead of the keys not found; the
  C checker then failed the affected jobs ("torus not implied"), the expected outcome of a wrong mark.
- From the first n = 7 build: caches of 2^20 slots overflowed in subtrees with up to 2.5M relation pairs (the check
  failed, as a full cache must); caches are now sized per job, from 2^14 to 2^23 slots. A lookup shortcut above the
  reset level put the stream out of step; it is limited to positions below that level.
- The branching order of the refutation search was chosen by a C prototype. Centre-out order needs 2,611 nodes to
  refute 17×17 for the n = 7 champion, against 219,481 for smallest-domain-first and 990,604 for scan order. On the
  closed claims of shards 1 and 31 it needs 22–25 nodes per claim (1,702 at most), against 6,800–8,800 for
  smallest-domain-first.

## The earlier route (part 1)

The proof published in part 1 checked the 64 v1 shards as they are: shard s walked the subtrees with index s
modulo 64, each shard's bytes and torus table were Rocq lists in one data file, and every key was stored. Its clean
build took 5,151 s on 20 cores, 16.5 core-hours, with jobs up to 9.8 GB and the final file at 10.7 GB
(`logs/build_clean_part1.log`). The statement, the theorems and the soundness argument are the same; the checker
changed in four places (job list, remember marks, shared torus table, data layout) and the proofs with it. The
part-1 sources are in the part-1 release.

## Limits

- **Two long jobs.** Jobs 0 and 1 each hold one subtree of the v1 tree at position 10 (302.9M and 272.5M nodes)
  and take about an hour. Both subtrees are a single deep path that carries most of the work down to depth about
  170 (`logs/n7_v4_notes.txt`), so cutting the tree at one deeper level does not split them. Splitting them would
  need jobs that start from an arbitrary prefix, with fresh tables and the certificate re-encoded for them; that
  was not done.
- **Core-hours.** The n = 7 checks still take 14.4 core-hours, against about 35 core-minutes for the C checker:
  the Rocq checker runs at 9.6 µs per node alone and 11 µs per node with 20 jobs at once, against 0.46 µs in C.
  Profiling shows the time spread over the symmetric skip (about 21%), the colour merges (17%), the repeat-skip
  key (10–15%), the cache keys and the closed claims, with no single hotspot; each speed-up would mean reworking
  part of the proof, and none was done here.
- **Memory.** The largest job is the n = 6 check in `WangTiles_Theorem.v` (3.3 GB), unchanged from part 1; n = 7
  jobs peak at 1.0–2.4 GB. Eight jobs at once typically need about 12 GB, at most about 16 GB.
- **Data size.** The n = 7 data are 775 MB of `.v`, regenerated from the v1 download, not stored.
- **Trusted base.** The kernel's `native_compute` evaluation, which includes the OCaml compiler and the kernel's
  implementation of primitive integers and arrays, as in any Rocq proof by native computation.
- **Not covered.** BB_WT(8): only the lower bound is claimed anywhere, and only it is proved. BB_WT(3) = 3 and
  BB_WT(4) = 4 have certificates that the checker passes, but they are not packaged as theorems here.
