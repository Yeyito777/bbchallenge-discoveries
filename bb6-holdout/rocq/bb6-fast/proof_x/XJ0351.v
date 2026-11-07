From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z351 XCuts.b351 XCuts.z352 XCuts.b352 XCuts.n351 XCuts.v351 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
