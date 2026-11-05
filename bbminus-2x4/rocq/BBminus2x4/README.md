# BB^-(2,4) < BB(2,4)

This folder is a Coq (Rocq 8.20.1) proof that on the start tape `110[1]011` every halting 2-state 4-symbol Turing
machine halts within 1,845,977 steps, and that one machine takes exactly that many. Since the BB(2,4) champion takes
3,932,964 steps from the blank tape, it follows that BB^-(2,4) <= 1,845,977 < 3,932,964 <= BB(2,4).

BB_init(n,m,T) is the longest runtime of an n-state m-symbol machine that halts when started in state A on tape T, and
BB^-(n,m) is the least BB_init(n,m,T) over all tapes T ([wiki](https://wiki.bbchallenge.org/wiki/Least_Busy_Beaver)).
This proof shows BB_init(2,4,`110[1]011`) = 1,845,977. It does not determine BB^-(2,4) itself.

It is built on Coq-BB5's proof of BB(2,4) = 3,932,964 ([CoqBB5/BB2x4](https://github.com/ccz181078/Coq-BB5/tree/main/CoqBB5/BB2x4),
mxdys, MIT): the same definitions, Tree Normal Form (TNF) enumeration and deciders, generalised from the blank tape to a
fixed start tape.

## Statement

`BBminus2x4_Statement.v` holds the definitions and statements. Everything above `End TM.` is Coq-BB5's `BB2x4_Statement.v`
unchanged. The start configuration is

```Coq
Definition StartTape (x:Z) : Σ :=
  match x with
  | (-3)%Z | (-2)%Z | 0%Z | 2%Z | 3%Z => Σ1
  | _ => Σ0
  end.

Definition StartES : ExecState Σ := (St0, StartTape).
```

that is, cells -3..3 hold `1 1 0 1 0 1 1`, the head is on cell 0, the state is A, every other cell is 0. Proved in
`BBminus2x4_Theorem.v`:

```Coq
Theorem BBinit2x4_StartTape_value: BBinit2x4_StartTape_statement.
(* (forall tm n0, HaltsAtPlusOne Σ tm n0 StartES -> n0 <= 1845977) /\
   (exists tm, HaltsAtPlusOne Σ tm 1845977 StartES) *)

Theorem BBminus2x4_lt_BB2x4: BBminus2x4_lt_BB2x4_statement.
(* exists t : Z -> Σ,
     (forall tm n0, HaltsAtPlusOne Σ tm n0 (St0, t) -> n0 <= 1845977) /\
     (exists tm, HaltsAtPlusOne Σ tm 3932964 (InitES Σ Σ0)) /\
     1845977 < 3932964 *)
```

Steps are counted as in Coq-BB5's BB(2,4) statement (`HaltsAtPlusOne`): the step that reaches the undefined transition
counts. Not counting it gives 1,845,976 against 3,932,963, so the inequality does not depend on this choice.

The machine reaching 1,845,977 steps is `2LA2LB0RB---_1RA3RB0RA1LB`; the champion is `1RB2LA1RA1RA_1LB1LA3RB---`. With
Coq-BB5's theorem `BB2x4_value` (BB(2,4) = 3,932,964) the last line is an equality; this proof does not need it, only the
champion's run, which it checks itself.

## Building

Install Coq 8.20.1 with `coq-native` as for Coq-BB5:

```sh
opam switch create rocq 4.14.2
eval $(opam env --switch=rocq)
opam pin add -n coq 8.20.1
opam install coq-native coq.8.20.1
```

Then, in this folder:

```sh
make -j8
```

### Compile time and memory

From a clean folder with `make -j8` on an AWS machine (AMD EPYC 9R14, 2026-11-04): 8 minutes 38 seconds, 61 CPU-minutes
in total (`../logs/clean_build_20261104.log`). Almost all of it is in the 72 files `TNF_Roots/Leaf_*.v`, which are
independent; the largest takes about 3 minutes. Each job needs up to 4.4 GB of memory, so use fewer jobs on a machine with
less (for example `make -j3` with 16 GB). On a Ryzen 5 3600XT a core is about 1.4 times slower.

### Axioms

`Print Assumptions` at the end of `BBminus2x4_Theorem.v` shows only

```Coq
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

the same axiom as Coq-BB5's BB(2,4) proof (tape contents and machines are functions).

## Proof structure

### Tree Normal Form enumeration from the start tape

The enumeration starts from the machine with no transitions. A machine is run from `StartES` through a pipeline of
deciders; if it reaches an undefined transition within 1,845,976 steps, all ways of filling that transition are enumerated
as its children, and if it never halts, it is a leaf. The root halts at once (state A reads 1). Two normalisations are used,
both proved in `TNF.v`:

- states: as in Coq-BB5, a new transition may go to state B before B is used;
- symbols (new): 2 and 3 do not occur on the start tape, so while no defined transition reads or writes either of them,
  they are interchangeable, and a new transition writing 3 is skipped in favour of the same one writing 2
  (`HaltTimeUpperBound_LE_swap23`). 0 and 1 are on the tape and are never exchanged.

Coq-BB5 also uses left/right symmetry for the first transition. That is not used here.

The enumeration visits 25,594,045 machines, as many as the C/Rust search and the independent Go/Python check in
`../../least` and `../../least-verify`, with the same numbers of halting (10,478,861) and non-halting machines (counted with an
OCaml extraction of the same code, `../explore/`).

It is split for parallel compilation like Coq-BB5's BB(5) proof: `TNF_Common.v` defines `node_at p`, the node reached from
the root by child indices `p`, and proves that a subtree whose search queue empties is bounded (`leaf_HTUB`) and that a node
is bounded when the pipeline says it halts and all its children are bounded (`inner_HTUB`). The root and four large subtrees
are inner nodes (`TNF_Enumeration.v`, `TNF_Roots/Inner_*.v`); the other 72 subtrees are leaves (`TNF_Roots/Leaf_*.v`), each
computed with `native_compute`. The files are generated by `../tools/gen_split.py`.

### Changes to Coq-BB5's code for a non-blank start tape

- `TM.v`, `List_Tape.v`: `StartES`, its list form `StartListES`, and the lemmas that used the blank start (state swaps,
  history alphabets) restated for a start configuration in state A;
- `Deciders/Decider_Loop.v`, `Decider_Halt.v`, `Verifier_Halt.v`: simulate from `StartListES`;
- `Deciders/Decider_NGramCPS.v`: the n-gram sets are seeded with every n-gram of the start tape and its local context,
  and the final check that the start configuration is in the closed set is proved for any tape given by finite lists
  (`check_InitES_InAES_spec`);
- `Deciders/Decider_RepWL.v`: the start configuration is the start tape cut into words of the decider's length, padded with 0
  (`In_RepWL_ES_StartES`);
- `Deciders/Decider_Halt_Max.v`: runs machines up to 1,845,977 steps; `BB2x4_Encodings.v`: the bound 1,845,976 in Coq-BB5's
  `HaltsAt` convention;
- `BB2x4_Deciders_Pipeline.v`, `BB2x4_Deciders_Generic.v`: the table decider added before the final halting check.

Coq-BB5's `_BB2x4_Legacy_Monolith.v`, extraction files and `copy_from_BB5.sh` are not included.

### Deciders

The pipeline (`BB2x4_Deciders_Pipeline.v`) is Coq-BB5's BB(2,4) pipeline with one decider added before the final halting
check. Counts from the extraction:

| Decider | Halt | Nonhalt |
| --- | ---: | ---: |
| Loops (107 steps), including the root | 10,459,199 | 14,348,570 |
| n-gram CPS, Coq-BB5's 12 parameter sets | | 702,146 |
| Loops (4,100 steps) | 19,522 | 29,586 |
| RepWL, Coq-BB5's 3 parameter sets | | 27,611 |
| n-gram CPS LRU, Coq-BB5's 2 parameter sets | | 6,289 |
| Table: per-machine n-gram CPS parameters | | 957 |
| Table: closed automaton certificates | | 25 |
| Halt max (1,845,977 steps) | 140 | |
| Total | 10,478,861 | 15,115,184 |

The table (`Deciders/Decider_Table.v`) maps a machine to the decider and parameters that decide it, like Coq-BB5's
hardcoded parameters for BB(5): 785 machines need larger n-gram CPS gas or windows (`TE_NG2`) and 172 need the per-cell
history variant (`TE_NG1`), found by a parameter sweep (`../tools/choose_table.py`). The remaining 25 machines get a closed
automaton certificate.

### Closed automaton certificates (new)

`Deciders/Verifier_ClosedAut.v` checks a certificate made of two automata reading the tape from far away towards the head
(one per side, over cell labels that stand for symbols, possibly with extra information), their blank-cycle states, and a
set of abstract configurations (left state, control, head cell, right state). It checks that the start configuration is in
the set and that every configuration in it has a defined transition whose results, for every way of popping the far side,
are again in the set; the soundness proof (`check_all_spec`) is an induction on the run. The 25 certificates
(`Deciders/ClosedAut_Certificates_*.v`, 349,883 configurations) come from `least-verify/certs/T_certs.xz` and were converted by
`../tools/certs_to_coq.py`. Among these machines are the run-language cases of the original search (closed languages over
run-compressed blocks), which Coq-BB5's deciders do not cover.

Soundness never depends on the table or the certificates: each entry is run through a decider proved sound for every
machine, so a wrong entry could only fail to decide its machine and break the build.

### Files

New: `BBminus2x4_Statement.v` (statement), `BBminus2x4_Theorem.v` (entry point), `TNF_Common.v`, `TNF_Enumeration.v`,
`TNF_Roots/`, `Deciders/Verifier_ClosedAut.v`, `Deciders/Decider_Table.v`, `Deciders/Table_Params.v`,
`Deciders/ClosedAut_Certificates*.v`. Every other file is Coq-BB5's, changed only as listed above. The git history of this
folder starts from Coq-BB5's files with only the logical path renamed (`CoqBB2x4` to `BBminus2x4`), so
`git diff 61cb395` shows every change.

## Credits

- Coq-BB5 and its BB(2,4) proof, deciders and proof structure: mxdys and the bbchallenge collaboration
  (https://github.com/ccz181078/Coq-BB5, MIT; see `LICENSE`).
- n-gram CPS: Nathan Fenner; Repeated Word List and the Coq implementations: mxdys.
- BB^- definition and the first certificates: racheline, Shawn Ligocki and others on the bbchallenge Discord (February 2025).
- The search on `110[1]011`, its ledger and the closed automaton certificates: `../../least/RESULT.md`,
  `../../least-verify/VERIFY.md`.
