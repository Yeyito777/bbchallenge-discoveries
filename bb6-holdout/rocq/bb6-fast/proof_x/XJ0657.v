From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z657 XCuts.b657 XCuts.z658 XCuts.b658 XCuts.n657 XCuts.v657 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
