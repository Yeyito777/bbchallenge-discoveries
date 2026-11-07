From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z299 XCuts.b299 XCuts.z300 XCuts.b300 XCuts.n299 XCuts.v299 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
