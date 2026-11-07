From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z667 XCuts.b667 XCuts.z668 XCuts.b668 XCuts.n667 XCuts.v667 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
