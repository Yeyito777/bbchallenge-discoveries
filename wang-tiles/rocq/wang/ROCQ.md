# Wang tiles lane: what is proved in Rocq

## Proved

In Rocq 8.20.1 with coq-native, from the definitions in `WangTiles_Statement.v` (the wiki's and the BB_WT thread's,
quoted in `wang/RESULT.md`):

- `BB_WT_5 : BB_WT_is 5 6`, `BB_WT_6 : BB_WT_is 6 8` and `BB_WT_7 : BB_WT_is 7 16`: exact values.
- `BB_WT_8_lower : BB_WT_at_least 8 17`: lower bound (`BB_WT_7_lower` is also kept).
- `plane_5`, `plane_6`, `plane_7`: every 5-tile set that tiles 7×7, every 6-tile set that tiles 9×9, and every 7-tile
  set that tiles 17×17 tiles the plane.

Each lower bound is a champion with an explicit tiling and a proved-sound search refusing the next size. Each
upper bound runs one checker, proved sound in Rocq, on the existing certificate, read byte for byte:
`wang/certs/upper/n5_D7_ringsym` (289,369 nodes), `n6_D9_ringsym` (69,208,331 nodes), and the 64 shards of
`wang/certs/n7/n7_D17` (4,537,499,086 nodes). The proof covers everything `check_cert.py` does:
- the symmetric skip and the repeat skip;
- the torus-to-plane step;
- closed claims (77,703 in the n = 7 certificate, 155,406 verifications counting repeats after resets), the visit
  gate, and the subtree resets shared out over shards;
- the step from tile lists to labels named by first appearance.

The cross-shard condition is checked exactly. Each shard's check compares its list of 5,519 recorded prefixes with
one reference list, element by element, and the reference list is shown duplicate-free by computation. No digest
or hash is trusted. The upper bounds hold for any list of n tiles, duplicates allowed, which is stronger than the
statement needs.

## Build time and memory

A clean build, from regenerating the data to `BB_WT_7`, took 5,151 s (86 minutes) on 20 cores of the shared AMD EPYC
9R14 box, 16.5 core-hours in all (`logs/build_clean.log`). Per job:

| Job | Time | Peak memory |
|---|---|---|
| each of the 64 shard checks (`n7/Check7_sNNN.v`) | 423–4,874 s, median 705 s | 2.0–9.8 GB |
| each of the 64 shard data files (`n7/Cert7_sNNN.v`) | 39–82 s | 1.6–2.6 GB |
| `WangTiles_Theorem7.v` (loads all shards; NoDup of the prefixes 24 s) | 81 s | 10.7 GB |
| `WangTiles_Theorem.v` (n = 5 check 3 s, n = 6 check 683 s, champions 6 s) | 695 s | 3.1 GB |
| all proof files together | under 10 s | under 0.5 GB |

Shard 0 (410M nodes) sets the critical path at 4,874 s. Shard 2 (328M nodes) takes 4,535 s, every other shard under
1,700 s. n = 7 runs at 10–14 µs per node in Rocq, against 0.46 µs for the C checker on the same shard. `make small`
builds n = 5, 6 and 8 alone in about 12 minutes on one core.

## Axioms

The lower bounds are closed. The upper bounds list only Rocq's primitive integers and arrays (the types and their
operations). No axiom about them is used, so the proofs do not depend on what they compute; they carry the
certificate data and caches whose answers are always re-checked. See `README.md`.

## How to check it

```sh
cd rocq/wang
tools/make_n7.sh ../../wang/certs/n7    # checks SHA256SUMS, writes n7/Cert7_*.v and n7/Check7_*.v
make -j20                               # needs coq 8.20.1 + coq-native, as Coq-BB5
make small                              # n = 5, 6, 8 only, no n = 7 data needed
```

The data files are generated from `wang/certs/` with `tools/cert_to_coq.py` (and `tools/champions_to_coq.py`).
Each generated file records the SHA-256 of the certificate files it was made from, and `tools/make_n7.sh` compares
the 128 generated n = 7 files with `n7/MANIFEST.sha256`. A reader downloads the 195 MB certificate once and gets
byte-identical data files. The reference prefix list `n7/Wang7_Prefixes.v` (122 KB) is kept in the folder; it was
produced by `tools/c/prefixes.c` (check_cert.c plus one print). Its contents need no trust, because every shard is
checked against it exactly.

## Tests beyond the build

- The same checker passes the n = 3 and n = 4 certificates (`n3_D4_ringsym`, `n4_D5_ringsym`).
- It rejects four corrupted copies of the n = 5 certificate: three with one torus id changed, one cut in half.
- A first n = 7 build with caches of 2^20 slots failed shards 14, 38, 40 and 42, where a single subtree holds up to
  2.5M relation pairs (`logs/n7_c_stats/`). A full cache makes the check fail and can never make it pass, which is
  how the problem showed. The caches are now 2^23 slots.
- An early version skipped the relation-table lookup for a child whose relations equal its parent's even above
  the reset level, where a sibling's reset may have cleared the table in between. Shard 31 then failed, because
  the token stream fell out of step. The skip is now limited to positions below the reset level, and shard 31
  passes, with all 5,809,062 bytes read and its 5,519 prefixes equal to the reference list.
- The branching order of the refutation search was chosen by a C prototype. Centre-out order needs 2,611 nodes to
  refute 17×17 for the n = 7 champion, against 219,481 for smallest-domain-first and 990,604 for scan order. On the
  closed claims of shards 1 and 31 it needs 22–25 nodes per claim (1,702 at most), against 6,800–8,800 for
  smallest-domain-first.

## Limits

- **Build time.** The n = 7 checks dominate: 15.4 core-hours, against about 35 core-minutes for the C checker.
  Shard 0 alone takes 81 minutes, so the build cannot finish faster than that however many cores it gets.
  Splitting a shard further would need a reader that can jump over subtrees in the byte stream. That is not done.
- **Memory.** Shard jobs peak at 2.0–9.8 GB, and the final theorem file at 10.7 GB because it loads all 64 shards.
  With 20 jobs the box had about 50 GB in use, other lanes' work included. This is far beyond Coq-BB5's BB(2,4) proof. The n = 5 and 6
  results alone (`make small`) need 3.1 GB.
- **Data size.** The n = 7 data is 1.1 GB of `.v` (from 195 MB compressed) and is regenerated, not stored.
- **Trusted base.** The kernel's `native_compute` evaluation, which includes the OCaml compiler and the kernel's
  implementation of primitive integers and arrays, as in any Rocq proof by native computation.
- **Not covered.** BB_WT(8): only the lower bound is claimed anywhere, and only it is proved. BB_WT(3) = 3 and
  BB_WT(4) = 4 have certificates that the checker passes, but they are not packaged as theorems here.
