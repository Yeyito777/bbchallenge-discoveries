From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z684 XCuts.b684 XCuts.z685 XCuts.b685 XCuts.n684 XCuts.v684 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
