# Rocq proof of BB^-(2,4) < BB(2,4)

## What is proved in Rocq

On the start tape `110[1]011` (cells -3..3 = 1 1 0 1 0 1 1, head on cell 0, state A, 0 elsewhere):

- every 2-state 4-symbol machine that halts does so within 1,845,977 steps, and `2LA2LB0RB---_1RA3RB0RA1LB` takes exactly
  1,845,977 (`BBinit2x4_StartTape_value`), so BB_init(2,4,`110[1]011`) = 1,845,977;
- hence (`BBminus2x4_lt_BB2x4`): there is a tape on which every halting machine stops within 1,845,977 steps, and the
  champion `1RB2LA1RA1RA_1LB1LA3RB---` takes 3,932,964 steps from the blank tape. So BB^-(2,4) <= 1,845,977 < 3,932,964 <= BB(2,4).

The halting step is counted (Coq-BB5's `HaltsAtPlusOne`, the convention of BB(2,4) = 3,932,964 and BB(5) = 47,176,870).
The inequality uses the champion's run, which this proof checks itself, not Coq-BB5's BB(2,4) theorem; with that theorem the
last `<=` is an equality.

The proof is in `BBminus2x4/`; its `README.md` has the statement, build steps and structure. The statement file is
`BBminus2x4/BBminus2x4_Statement.v` (Coq-BB5's definitions plus the start tape and the two statements).

## How it is built

Coq-BB5's `CoqBB5/BB2x4` proof, generalised from the blank tape to a start tape:

- TNF enumeration from `110[1]011`, with the state normalisation of Coq-BB5 and a new, proved symbol normalisation (2 and 3
  are interchangeable until one is read or written). No left/right reduction. 25,594,045 machines with 10,478,861 halters,
  the same counts as the original C/Rust search and the independent Go/Python check.
- Coq-BB5's deciders (loops, n-gram CPS in three variants, Repeated Word List, halting up to the bound), changed to start
  from the tape: the loop and halting deciders simulate from it, n-gram CPS is seeded with all n-grams of the start tape and
  proves that the start configuration is in the closed set, RepWL cuts the start tape into words.
- Coq-BB5's BB(2,4) pipeline leaves 982 machines open on this tape. 957 are decided by the same deciders with per-machine
  parameters (a table, as Coq-BB5 does for BB(5)). The other 25, including the run-language cases, are decided by a new
  verifier of closed automaton certificates (`Deciders/Verifier_ClosedAut.v`, with a soundness proof), fed the certificates
  of `least-verify/certs/T_certs.xz` (349,883 configurations). Soundness does not depend on any table entry or certificate.
- The tree is split into 72 subtrees compiled in parallel, as in Coq-BB5's BB(5) proof.

## Compile time, memory, axioms

- Clean build, plain `make -j8`, AMD EPYC 9R14 (an AWS machine): 8 minutes 38 seconds, 61 CPU-minutes in total
  (`logs/clean_build_20261104.log`). On a Ryzen 5 3600XT a core is about 1.4 times slower.
- Up to 4.4 GB of memory per parallel job.
- `Print Assumptions` shows only `functional_extensionality_dep`, as for Coq-BB5's BB(2,4) proof. As in Coq-BB5 the kernel
  check of the enumeration uses `native_compute`, so the OCaml native compiler is part of what is trusted.

## How someone checks it

1. Read `BBminus2x4/BBminus2x4_Statement.v` (about 150 lines; the part above `End TM.` is Coq-BB5's).
2. Install Coq 8.20.1 with `coq-native` (commands in the README) and run `make -j8` in `BBminus2x4/`.
3. Check the `Print Assumptions` output at the end of the build log.

The rest need not be trusted. To see what changed from Coq-BB5: `changes-from-coq-bb5.patch` here is the diff against Coq-BB5's files with only the
logical path renamed, leaving out the generated `Deciders/ClosedAut_Certificates_*.v`; `upstream/` holds the original files.

## What is not proved, and why

- BB^-(2,4) itself: only the upper bound 1,845,977. Smaller values may exist on larger tapes (RESULT.md).
- The other-tape results in `least/RESULT.md` (the census of 1,451 tape classes, periodic backgrounds, the 8-instruction
  machine) are not formalised.
- The per-decider counts in the README come from an OCaml extraction of the same Coq code (`explore/`), not from the proof,
  which only proves the bound. Coq-BB5 ships an extraction script that prints them; this folder does not.

## Tools and data

- `tools/gen_split.py`: writes the subtree files. `tools/choose_table.py`, `tools/gen_table.py`, `tools/certs_to_coq.py`:
  turn the parameter sweep and the certificates into `Deciders/Table_Params.v` and `Deciders/ClosedAut_Certificates*.v`.
- `explore/`: extraction-based exploration (undecided machines per subtree, parameter sweeps). Not part of the proof. Sources only here; sweep outputs are not shipped.
- `data/unk_certs.xz`: the 982 certificates of `T_certs.xz` for the machines left open by Coq-BB5's pipeline.
- `logs/`: the clean build log.
- `upstream/`: the Coq-BB5 BB2x4 folder this was built from (commit 9142e21, MIT).

Toolchain: opam switch `rocq` (OCaml 4.14.2, coq 8.20.1 pinned, coq-native).
