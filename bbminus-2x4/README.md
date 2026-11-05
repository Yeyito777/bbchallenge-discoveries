# BB^-(2,4) ≤ 1,845,977 < 3,932,964 ≤ BB(2,4)

Proved in Rocq, on the start tape `110[1]011`. The statement is [`rocq/BBminus2x4/BBminus2x4_Statement.v`](rocq/BBminus2x4/BBminus2x4_Statement.v), about 150 lines. See [`rocq/ROCQ.md`](rocq/ROCQ.md) and [`rocq/BBminus2x4/README.md`](rocq/BBminus2x4/README.md) for the proof, [`least/RESULT.md`](least/RESULT.md) for the search and the census of other tapes, and [`least-verify/VERIFY.md`](least-verify/VERIFY.md) for the independent check.

## Build the proof

```sh
opam switch create rocq 4.14.2 && eval $(opam env --switch=rocq)
opam pin add -n coq 8.20.1 && opam install coq-native coq.8.20.1
cd rocq/BBminus2x4
make -j8
```

Expected: 8 to 9 minutes with 8 jobs on AMD EPYC 9R14, 61 CPU-minutes, up to 4.4 GB per job (use `make -j3` with 16 GB). `Print Assumptions` at the end shows only `functional_extensionality_dep`. Reference log: [`rocq/logs/clean_build_20261104.log`](rocq/logs/clean_build_20261104.log).

## What differs from Coq-BB5

`rocq/upstream/` is Coq-BB5's `BB2x4` folder (commit 9142e21). [`rocq/changes-from-coq-bb5.patch`](rocq/changes-from-coq-bb5.patch) is the full diff from those files with the logical path renamed, leaving out the generated `Deciders/ClosedAut_Certificates_*.v`. The original repository's history isn't shipped.

## Check without Rocq

See "How to rerun and check" in `least/RESULT.md` and "Rerun" in `least-verify/VERIFY.md`. The ledger check takes about 26 minutes on 3 threads and 5 GB. The certificate check takes about 5 minutes and needs only Python.

## Licence

MIT, code and data alike: [`LICENSE`](LICENSE), Copyright (c) 2026 Yeyito (https://github.com/Yeyito777). The proof adapts Coq-BB5 by mxdys et al.: `rocq/BBminus2x4/LICENSE` is Coq-BB5's MIT notice, unchanged, and `rocq/BBminus2x4/LICENSE.Yeyito` covers our changes. `rocq/upstream/` keeps Coq-BB5's notice too.

## Assets

`bbminus-ledger` (the full search ledger), `bbminus-verify-certs` (585,826 independent certificates), `bbminus-verify-walk` (the independent walk's output). The Rocq build needs none of them.

`hunt.py`, `scan.sh`, `census.py` and `status.sh` from the search are left out because they only drove runs on our machines. The tape list method is `least/code/tapes.py`, and the results are in `least/certs/kills.txt`.
