From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z685 XCuts.b685 XCuts.z686 XCuts.b686 XCuts.n685 XCuts.v685 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
