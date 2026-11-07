From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z544 XCuts.b544 XCuts.z545 XCuts.b545 XCuts.n544 XCuts.v544 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
