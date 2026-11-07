From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z637 XCuts.b637 XCuts.z638 XCuts.b638 XCuts.n637 XCuts.v637 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
