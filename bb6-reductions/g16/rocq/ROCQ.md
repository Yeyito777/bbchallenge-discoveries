# The 16-machine BB(6) group: Rocq

**Status: for each of the 16 machines, both directions are proved from the raw machine, with no axioms: the machine halts from
blank if and only if some stack of one explicit orbit has a top event with P + 2 = 2^k. This does not settle any of the machines.**
Whether such a stack exists is open.

## What is proved, and what is not

| Part | State |
|---|---|
| Machine halts ⇒ some stack of the orbit has a top event with P + 2 = 2^k | **Proved in Rocq**, all 16. `g16_NN` |
| Some stack of the orbit has such a top event ⇒ machine halts | **Proved in Rocq**, all 16. `g16_NN` |
| The exact map: until such a stack, the machine passes through the tape of every stack of the orbit, in order | **Proved in Rocq**, all 16. `g16_map_NN` |
| The first 30,000 stacks of the orbit have no such top event | **Proved in Rocq**, by kernel computation. `no_hit_below` in `theories/Check.v` |
| No stack of the orbit has such a top event, or some stack does | **Not proved.** This is the open question |
| The orbit up to 2e10 map steps has no such top event, reaching P = 1.09e10 | **Not in Rocq.** A C run, `../analysis/lm.c`, checked against raw only as far as `../analysis/REPORT.md` says |
| Raw step counts | **Not proved.** The rules are `-->+` statements without counts |

So the theorem turns 16 machines into one question about one sequence. Settling that question either way settles all 16 at once.

The statement, from `theories/Statement.v`, for each machine `M`:

```coq
Theorem g16_NN : halts (TM_from_str "M") c0 <-> exists n, hit (orbit n).

Theorem g16_map_NN n : (forall k, (k < n)%nat -> ~ hit (orbit k)) ->
  c0 -[ (TM_from_str "M") ]->+ Cc a c (orbit n).
```

`g16_NN` is always about the literal machine. In `g16_map_NN`, machines 03, 04, 05 and 14 are stated on `mirror (TM_from_str "M")`,
since their tapes run the other way. `a` is the machine's right-walking state and `c` is 1 or 2 by family.

The map, from `theories/Spec.v`. It mentions no machine. A stack is a list of run lengths, rightmost run first.

```coq
Definition step (s : list nat) : list nat := match s with [] => [] | x :: t => carry (x + 2) t end.
Definition s0 : list nat := [9; 10].
Definition orbit (n : nat) : list nat := Nat.iter n step s0.
Definition pw (P : nat) : Prop := exists k, P + 2 = 2 ^ k.
Definition hit (s : list nat) : Prop := exists P, topP s = Some P /\ pw P.
```

`Cc a c s` in `theories/Tape.v` is the tape `1^c 0 1^4 0 1^6 0 1^s1 0 1^s2 ...` with the head in state `a` on the blank just to its right.

`theories/Check.v` computes the map in the kernel. It gives the top events P = 23, 21, 24, 104, 1290, 647, 7146 and 93998, the same as the
table in `../analysis/REPORT.md` and `lm.c`. Index n in Rocq is step n + 1 in that table.

## How the proof goes

1. `theories/Spec.v`: the map.
2. `theories/Generic.v`: an interface of eight transitions on abstract tapes, one for each move of the map, gives the map theorem and the if and only if.
   The interface is about stacks of the shape the orbit keeps (`Inv`).
3. `theories/Fam1.v`, `theories/Fam2.v`: the two families (right edge 6, 4, 1 and 6, 4, 2). Each derives the interface from about ten raw rules.
4. `theories/M01.v` to `theories/M16.v`: each proves the raw rules from the literal machine table, by stepping it with two walking lemmas.
   These files are generated from `gen/table.txt` and `gen/template1.v`, `gen/template2.v` by `gen/gen.py`.
5. `theories/Tape.v`: tape shapes, walking lemmas, and the mirror image of a machine (`mirror_halts`), proved without function extensionality.

Before the proofs, every rule was tested numerically on all 16 machines (`gen/ruletest2.py`). They all passed. The Rocq rules are stated in that form.

## Build and check

Rocq 8.20.1, no other libraries (`busycoq/` is included). From this directory:

```
make
```

A clean build took 27 min 16 s on one core (`logs/build_clean_j1.log`, AWS hunt box). At `make -j3` it took about 10.5 min. Each machine file takes about 90 s.

`make` ends by compiling `demo/Axioms.v`, which runs `Print Assumptions` on all 33 theorems. Every one prints `Closed under the global context`.
The output is in `logs/build_clean_j1.log`.

To check the machines the proof is about: `grep TM_from_str theories/Statement.v`. The 16 strings are `../analysis/g16_members.txt`.

## Trusted base

Rocq's kernel, and the definitions of `TM`, `halts` and `TM_from_str` in `busycoq/TM.v` and `busycoq/Individual62.v`. There are no axioms.
`vm_compute` is used only in `theories/Check.v`.

## Credits

The machine framework in `busycoq/` is a subset of `ccz181078/busycoq` branch BB6 (commit 4ea6784), MIT, with its licence files kept.
