# Busy Beaver results, with proofs

Results from the [Busy Beaver Challenge](https://bbchallenge.org) community's open questions. AI agents (Claude Opus) did the work, starting from [bbchallenge-corpus](https://github.com/Yeyito777/bbchallenge-corpus). All code was written by AI and has not yet been reviewed by a human. Please check it rather than trust it: each folder says how.

| Folder | Result | Checked by |
|---|---|---|
| [`wang-tiles/`](wang-tiles/README.md) | BB_WT(5) = 6, BB_WT(6) = 8, BB_WT(7) = 16, BB_WT(8) ≥ 17 | Rocq proof, standalone certificate checkers, separate searches |
| [`bbminus-2x4/`](bbminus-2x4/README.md) | BB^-(2,4) ≤ 1,845,977 < BB(2,4), on tape `110[1]011` | Rocq proof adapted from Coq-BB5, independent Go and Python check |

More results to follow.

## Large files

Certificates and logs are not in the tree. They are attached to the [v1 release](https://github.com/Yeyito777/bbchallenge-discoveries/releases/tag/v1), listed in [`ASSETS.md`](ASSETS.md) with their checksums. Each archive unpacks in place from the top of the repository:

```sh
gh release download v1 --repo Yeyito777/bbchallenge-discoveries
sha256sum -c SHA256SUMS
tar --zstd -xf ASSET.tar.zst -C .
```

## Layout

Each folder keeps the names the original write-ups use, so their relative paths work. `RESULT.md`, `VERIFY.md` and `ROCQ.md` are those write-ups, with a note at the top where a later proof has overtaken them. Check logs cited in them are in the `evidence-logs` asset.

## Licence

Everything in this repository, code, proofs, data and certificates alike, including the release assets, is under the MIT licence: [`LICENSE`](LICENSE), Copyright (c) 2026 Yeyito (https://github.com/Yeyito777).

Code that derives from other projects keeps their notices, and ours sits alongside them: `bbminus-2x4/rocq/BBminus2x4/` adapts Coq-BB5 by mxdys et al. `LICENSE` there is Coq-BB5's MIT notice, unchanged; `LICENSE.Yeyito` covers our changes. `bbminus-2x4/rocq/upstream/` is Coq-BB5's own files with its notice. `bbminus-2x4/rocq/explore/` reuses the same deciders under the same notices.

Short quotes from the bbchallenge wiki stay CC BY 4.0, by its contributors.
