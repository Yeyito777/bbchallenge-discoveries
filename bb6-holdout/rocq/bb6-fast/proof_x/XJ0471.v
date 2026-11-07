From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z471 XCuts.b471 XCuts.z472 XCuts.b472 XCuts.n471 XCuts.v471 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
