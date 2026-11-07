From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z553 XCuts.b553 XCuts.z554 XCuts.b554 XCuts.n553 XCuts.v553 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
