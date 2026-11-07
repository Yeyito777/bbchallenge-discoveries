From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z566 XCuts.b566 XCuts.z567 XCuts.b567 XCuts.n566 XCuts.v566 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
