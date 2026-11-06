# `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` halts

**Independently rebuilt:** a full from-source run of `run_all.sh` alone on a separate 128-core AWS machine (Nov 5-6 2026) passed all 313 jobs with no failures in 2 h 37 min, peak 1.6 GB per job, and produced a byte-identical `Final.vo` with the same 41 assumptions (`rocq/bb6-fast/run_out/verify_rebuild.log`). That run was interrupted twice by spot reclaims; finished jobs were kept and resumed.

The halt is a closed Rocq theorem, proved in the kernel with no extracted code:

```coq
Theorem bb6_holdout_halts : halts tm c0.
```

with `tm` the machine and `c0` the blank tape, as defined in busycoq. It is in [`rocq/bb6-fast/proof/Final.v`](rocq/bb6-fast/proof/Final.v), checked with `native_compute`. All 313 jobs passed: 275 core-hours, 2 h 40 min on 128 cores, at most 1.55 GB per job (about 34 hours and 13 GB on an 8-core desktop, scaled from that run). `Print Assumptions` lists 41 items, all Rocq primitives: `PrimInt63` (16), `Uint63` (13) and `PArray` (12). Like Coq-BB5's proofs, it trusts `ocamlopt` through `native_compute`; the kernel VM avoids that at about 1,500 core-hours (extrapolated, not run). See [`rocq/bb6-fast/README.md`](rocq/bb6-fast/README.md).

The exact step count, 6448902863343978619509980365051027907909194602118636181048891434378153619188134 counting the halting transition, comes from two independent computations that agree. One is an earlier Rocq-proved checker extracted to OCaml, which passed all 318,760 chunks in 2,722 core-hours ([`rocq/bb6/ROCQ.md`](rocq/bb6/ROCQ.md)). The other is the C traversal ([`bb6-orbit/RESULT.md`](bb6-orbit/RESULT.md)). That count also trusts the extraction, the OCaml compiler, `extract/main.ml` and `cert/assemble.py`. It isn't a closed theorem yet.

## Build the kernel proof

Needs Rocq 8.20.1 with native compilation, ideally on an OCaml 4.14 flambda switch (about 2x faster), and GMP:

```sh
opam switch create rocq-fl --packages=ocaml-variants.4.14.2+options,ocaml-option-flambda
eval $(opam env --switch=rocq-fl)
opam install coq.8.20.1 coq-native
cd rocq/bb6-fast
./run_all.sh          # one job per core; ./run_all.sh N for N jobs. Restartable. Needs no assets.
```

It builds `theories/`, runs the 313 jobs in `proof/` and compiles `proof/Final.v`, whose `Print Assumptions` goes to `proof/Final.out`. Expected: `run_out/proof/Final.out`, and the `.vo` hashes in `run_out/vo.sha256`. Per-job times and memory from the run are in `run_out/log/times.txt`. `gen/gen_final.py` regenerates `proof/` from `rocq/bb6/cert/chunks.tsv` (the `bb6-chunks` asset).

## Build the extracted checker (exact count)

Needs Coq 8.20.1. The checker build also needs OCaml's `coq-core` package.

```sh
cd rocq/bb6
make              # proofs and Print Assumptions: about 2 min on one core
make extract      # extract/check, the OCaml checker
make demo         # the first chunk inside the kernel with native_compute: about 2 min
```

`Print Assumptions` (end of the `make` output) should list only the primitive 63-bit integers and their specs. Reference log: [`rocq/bb6/logs/clean_build.log`](rocq/bb6/logs/clean_build.log). A clean rebuild with `make -j4` took 2:05 and 1.0 GB.

## Run the chain

Unpack `bb6-chunks`, which gives `rocq/bb6/cert/chunks.tsv`. One chunk:

```sh
extract/check seg 6 1 6 20345673609576897    # about 19 s
```

Any line of `chunks.tsv` (chunk id, segment id, z, B, z1, Y) checks the same way. Whole chain, 2,722 core-hours on the run, restartable, chunks independent:

```sh
cert/run_chain.sh WORKERS OUT extract/check cert/chunks.tsv
python3 cert/assemble.py cert/chunks.tsv ../../bb6-orbit/certs/seglist.txt ../../bb6-orbit/certs/segments OUT/res_*.tsv
```

To recheck the published run without rerunning it, unpack `bb6-chain-results` and use `run/out*/res_*.tsv` in the same `assemble.py` command. Expected output: `logs/assemble.txt`. `cert/mkspot.py` restates chunks as lemmas for the kernel (`logs/kernel_spot.log`).

`assemble.py` checks every link and compares each segment with `seg.c`'s result. The run used the flambda build (`extract/build_fl.sh`, about 25% faster), which needs a separate OCaml switch.

## The C traversal

`bb6-orbit/code/`, gcc ≥ 14. See "Rerun and check" in `bb6-orbit/RESULT.md`. `certs/segments/` holds one result per segment. A full replay is about 339 core-hours, and `replay_segment.sh ID` reruns one segment. The Lean bridge is `bb6-orbit/code/lean/AMapBridge.lean`, built against google-deepmind/cryptids commit c86f158.

## Licence

MIT, code and data alike: [`LICENSE`](LICENSE), Copyright (c) 2026 Yeyito (https://github.com/Yeyito777). `rocq/bb6/busycoq/` is a subset of busycoq and keeps its own MIT notices (`LICENSE`, `LICENSE-LibTactics`). The Lean bridge is ours; the cryptids repo it builds against is Apache-2.0 and isn't included.

## Assets

`bb6-chunks` (the chunk list), `bb6-samples` (reset states sampled about every 2^24 phases, input to `cert/mkchunks.py`, usable for replaying any stretch), `bb6-chain-results` (the checker's output per chunk). `evidence-logs-bb6` (check logs). All in the v2 release.

Scripts that only drove runs on our machines (`burst*`, `monitor.sh`, `run_worker.sh`) are left out.
