From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z683 XCuts.b683 XCuts.z684 XCuts.b684 XCuts.n683 XCuts.v683 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
