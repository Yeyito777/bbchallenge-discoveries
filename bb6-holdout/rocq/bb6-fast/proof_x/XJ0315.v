From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z315 XCuts.b315 XCuts.z316 XCuts.b316 XCuts.n315 XCuts.v315 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
