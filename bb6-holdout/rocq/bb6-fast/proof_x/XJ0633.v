From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z633 XCuts.b633 XCuts.z634 XCuts.b634 XCuts.n633 XCuts.v633 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
