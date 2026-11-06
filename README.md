# Busy Beaver results, with proofs

Results from the [Busy Beaver Challenge](https://bbchallenge.org) community's open questions. AI agents (Claude Opus) did the work, starting from [bbchallenge-corpus](https://github.com/Yeyito777/bbchallenge-corpus). All code was written by AI and has not yet been reviewed by a human. Please check it rather than trust it: each folder says how.

| Folder | Result | Checked by |
|---|---|---|
| [`wang-tiles/`](wang-tiles/README.md) | BB_WT(5) = 6, BB_WT(6) = 8, BB_WT(7) = 16, BB_WT(8) ≥ 17 | Rocq proof, standalone certificate checkers, separate searches |
| [`bbminus-2x4/`](bbminus-2x4/README.md) | BB^-(2,4) ≤ 1,845,977 < BB(2,4), on tape `110[1]011` | Rocq proof adapted from Coq-BB5, independent Go and Python check |
| [`bb6-holdout/`](bb6-holdout/README.md) | `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` halts in about 6.45×10^78 steps | Closed Rocq proof of `halts tm c0` in the kernel; exact step count from an extracted Rocq-proved checker and a C traversal |

## Large files

Certificates and logs are not in the tree. They are attached to two releases, [v1](https://github.com/Yeyito777/bbchallenge-discoveries/releases/tag/v1) (Wang tiles, BB^-) and [v2](https://github.com/Yeyito777/bbchallenge-discoveries/releases/tag/v2) (BB(6)), listed in [`ASSETS.md`](ASSETS.md) with their checksums. Each archive unpacks in place from the top of the repository:

```sh
gh release download TAG --repo Yeyito777/bbchallenge-discoveries
sha256sum -c SHA256SUMS
tar --zstd -xf ASSET.tar.zst -C .
```

## Layout

Each folder keeps the names the original write-ups use, so their relative paths work. `RESULT.md`, `VERIFY.md` and `ROCQ.md` are those write-ups, with a note at the top where a later proof has overtaken them. Check logs cited in them are in the `evidence-logs` and `evidence-logs-bb6` assets.

## Licence

Everything in this repository, code, proofs, data and certificates alike, including the release assets, is under the MIT licence: [`LICENSE`](LICENSE), Copyright (c) 2026 Yeyito (https://github.com/Yeyito777).

Code that derives from other projects keeps their notices, and ours sits alongside them:

- `bbminus-2x4/rocq/BBminus2x4/` adapts Coq-BB5 by mxdys et al. `LICENSE` there is Coq-BB5's MIT notice, unchanged; `LICENSE.Yeyito` covers our changes. `bbminus-2x4/rocq/upstream/` is Coq-BB5's own files with its notice. `bbminus-2x4/rocq/explore/` reuses the same deciders under the same notices.
- `bb6-holdout/rocq/bb6/busycoq/` is a subset of busycoq, with its `LICENSE` and `LICENSE-LibTactics`, both MIT.

Short quotes from the bbchallenge wiki stay CC BY 4.0, by its contributors.
