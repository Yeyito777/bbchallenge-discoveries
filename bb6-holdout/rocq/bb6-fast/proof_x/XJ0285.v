From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z285 XCuts.b285 XCuts.z286 XCuts.b286 XCuts.n285 XCuts.v285 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
