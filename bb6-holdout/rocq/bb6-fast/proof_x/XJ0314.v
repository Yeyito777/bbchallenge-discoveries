From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z314 XCuts.b314 XCuts.z315 XCuts.b315 XCuts.n314 XCuts.v314 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
