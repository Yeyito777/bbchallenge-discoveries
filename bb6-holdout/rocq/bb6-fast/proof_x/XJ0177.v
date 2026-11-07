From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z177 XCuts.b177 XCuts.z178 XCuts.b178 XCuts.n177 XCuts.v177 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
