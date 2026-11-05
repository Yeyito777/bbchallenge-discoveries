# BB_WT(5) = 6, BB_WT(6) = 8, BB_WT(7) = 16, BB_WT(8) ≥ 17

Proved in Rocq. The statement is [`rocq/wang/WangTiles_Statement.v`](rocq/wang/WangTiles_Statement.v), about 60 lines: read that first. The proof is explained in [`rocq/wang/README.md`](rocq/wang/README.md) and [`rocq/wang/ROCQ.md`](rocq/wang/ROCQ.md), the searches and checkers in [`wang/RESULT.md`](wang/RESULT.md).

## Earlier work

Jeandel and Rao named this quantity: in "An aperiodic set of 11 Wang tiles" (Advances in Combinatorics 2021:1, [arXiv:1506.06492](https://arxiv.org/abs/1506.06492), Section 8, Conjecture 2), f(n) is the smallest k such that every Wang set of size n that does not tile the plane does not tile a k×k square, so f(n) = BB_WT(n) + 1. They give no values, so as far as we can find these are the first: f(5) = 7, f(6) = 9, f(7) = 17.

## Build the proof

Needs Coq 8.20.1 with coq-native and OCaml 4.14.2.

```sh
opam switch create rocq 4.14.2 && eval $(opam env)
opam install coq-native && opam pin add coq 8.20.1
cd rocq/wang
make small                               # n = 5, 6, 8: about 12 min on one core, 3.1 GB, no assets
tools/make_n7.sh ../../wang/certs/n7 8   # needs wang-certs-n7; about 43 core-minutes; checks SHA256SUMS and n7/MANIFEST.sha256
make -j8                                 # n = 7 as well (-j6 on a 16 GB machine)
```

| Target | Time | Memory |
|---|---|---|
| `make small` | about 12 min, 1 core | 3.1 GB |
| `tools/make_n7.sh` | about 43 core-minutes (4 min with 16 jobs) | up to 2.5 GB per process |
| `make -j8` | about 2 hours on 8 cores, about 15.3 core-hours. Two of the 72 jobs take about an hour each, the rest 10 to 17 minutes | up to 3.3 GB per job, about 12 GB in all with 8 jobs |

Measured: `make -j20` on AMD EPYC 9R14 from the v1 download took 64 minutes, peak 3.3 GB per job. The first published version of this proof needed up to 10.7 GB per job; its log is `rocq/wang/logs/build_clean_part1.log` and `rocq/wang/ROCQ.md` describes the change.

`Print Assumptions` runs at the end of each theorem file. Expected: `BB_WT_8_lower` closed; the others only the 16 built-in `PrimInt63`/`PArray` primitives. Reference log: [`rocq/wang/logs/build_clean.log`](rocq/wang/logs/build_clean.log).

## Check without Rocq

```sh
cd wang       # with wang-certs-upper, wang-certs-n7 and wang-certs-champions unpacked
gcc -O2 -o check_cert code/check_cert.c
python3 code/check_cert.py certs/upper/n5_D7_shell     # standard library only
./check_cert certs/upper/n6_D9_ringsym                 # under a minute
code/check_shards.sh ./check_cert certs/n7 n7_D17 64 2 # about 30 min on 2 cores
```

To regenerate certificates and histograms, see "How to rerun and check" in `wang/RESULT.md` (C and Rust, no dependencies). Each generated Rocq data file records the SHA-256 of its source certificate.

## Licence

MIT, code and certificates alike: [`LICENSE`](LICENSE), Copyright (c) 2026 Yeyito (https://github.com/Yeyito777).

## Assets

`wang-certs-n7` (n = 7 proof input), `wang-certs-upper` (n = 1 to 6 trees), `wang-certs-champions` (CNFs and DRAT/LRAT refutations; the tile lists and tilings are also in this tree).
