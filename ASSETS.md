# Release assets

Large files, kept out of the source tree and attached to three GitHub releases. Each archive unpacks in place from the top of the repository: `tar --zstd -xf NAME.tar.zst -C .`. Check them first with `sha256sum -c SHA256SUMS`. Everything is under the MIT licence, Copyright (c) 2026 Yeyito (https://github.com/Yeyito777); each archive carries a copy of `LICENSE` at its top, the same file as in the repository.

## [v1](https://github.com/Yeyito777/bbchallenge-discoveries/releases/tag/v1): Wang tiles and BB^-

| Name | Bytes | SHA-256 | What it is | Used by |
|---|---:|---|---|---|
| `wang-certs-n7.tar.zst` | 203,738,784 | `684ca83688e4e35c541936fe6381dec6ca7b2eae425046d9a460595c4d9eb48e` | n = 7 certificate at D = 17: 64 shards (trees and tori, xz) with SHA256SUMS | `wang-tiles/rocq/wang/tools/make_n7.sh` (Rocq proof); `wang/code/check_shards.sh` (C checker); `check_cert.py` |
| `wang-certs-upper.tar.zst` | 9,542,389 | `148cd1f2ac6c264300e2b6d7385a0999d9077f9e7982252282934c3e37c596e1` | n = 1 to 6 certificates, `ringsym` and `shell` orders | `check_cert.py`, `check_cert.c`; `tools/cert_to_coq.py` regenerates `Cert_n5_D7.v`, `Cert_n6_D9.v` |
| `wang-certs-champions.tar.zst` | 6,945,744 | `03bfd2f8e0c715a6e1275a663f421cc7bdad7feb1105ed482e0c43c00e279ec6` | Champions: tile lists, tilings, CNFs, DRAT and LRAT refutations of the next square, small tree certificates | `wang/code/check_proofs.sh`, `tools/champions_to_coq.py` |
| `bbminus-ledger.tar.zst` | 47,304,049 | `d3eb34fd3acfee6fadf3cfdb467dfdf6d0f4033994d2496395deecb8915b20b3` | Full search ledger on `110[1]011`: one record per machine, 25,594,045 records (xz) | `least/code/check` (Rust verifier). Not needed by the Rocq build |
| `bbminus-verify-certs.tar.zst` | 147,092,215 | `41f02d2f652bc6accf48c041da717c94b065936bc16eb9e80e955c3a17226654` | 585,826 independent closed-set certificates (xz) | `least-verify/code/check/check_cert.py`. Not needed by the Rocq build; `rocq/data/unk_certs.xz` holds the 982 the proof uses |
| `bbminus-verify-walk.tar.zst` | 73,059,683 | `45b0d6d39cd77a5870d3d3bc600fd7548eb8b2898972b7752ee35021e5b253ea` | Independent walk's class per machine, decider results per machine, blank-tape walk (xz) | Compared with the ledger; see `least-verify/VERIFY.md` |
| `evidence-logs.tar.zst` | 29,987 | `11a485714044df2b7a5f731391e507f9c9b3df0baa426ecd4742cad46ce57d71` | Check logs cited by `RESULT.md`, `VERIFY.md` and `ROCQ.md` for the Wang tiles and BB^- results | Read only |

## [v2](https://github.com/Yeyito777/bbchallenge-discoveries/releases/tag/v2): BB(6)

| Name | Bytes | SHA-256 | What it is | Used by |
|---|---:|---|---|---|
| `bb6-chunks.tar.zst` | 5,462,701 | `500aba0a1fab06aa43c6f53acd79b4a01af15f8646e93f2cbb19e7b348e87f58` | 318,760 chunks of the BB(6) chain: `chunk_id seg_id z B z1 Y` | `rocq/bb6/cert/run_chain.sh`, `rocq/bb6/cert/assemble.py` |
| `bb6-samples.tar.zst` | 6,888,071 | `cb604de911cd420dde1857a320cd8c1af3a51e4be1b1ffa35eda3a93aa378a56` | Reset states sampled about every 2^24 phases, per segment | `rocq/bb6/cert/mkchunks.py` (made `chunks.tsv`); replaying a stretch with `seg` |
| `bb6-chain-results.tar.zst` | 16,003,789 | `f9128da8142ed2a8c73b98bdb8d3af3913e71480c2137278a92f72dcc724d4bc` | Output of the extracted checker for every chunk, plus `assemble.py` output | `rocq/bb6/cert/assemble.py` |
| `evidence-logs-bb6.tar.zst` | 55,702 | `fcebcd2661839ba6b23fb38f64a2fb8ece3fb8d62aa8dec1f02d13ddf47fd2c4` | Check logs cited by the BB(6) `RESULT.md` | Read only |

## [v3](https://github.com/Yeyito777/bbchallenge-discoveries/releases/tag/v3): BB(6) logs

| Name | Bytes | SHA-256 | What it is | Used by |
|---|---:|---|---|---|
| `evidence-logs-v3.tar.zst` | 359,469 | `94f2d889efa365a179f84e329673f517161991086d697434b6aa7e82efe0a448` | Per-job logs of the BB(6) exact-count run (707 jobs); kernel job logs, done markers and per-job C and Rust step counts for `1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE` (523 jobs); that run's near-miss log | Read only; `bb6-holdout-2/kernel/sum_counts.py` sums the counts |
