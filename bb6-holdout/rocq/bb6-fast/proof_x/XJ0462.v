From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z462 XCuts.b462 XCuts.z463 XCuts.b463 XCuts.n462 XCuts.v462 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
