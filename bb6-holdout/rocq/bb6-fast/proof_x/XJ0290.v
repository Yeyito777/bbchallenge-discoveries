From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z290 XCuts.b290 XCuts.z291 XCuts.b291 XCuts.n290 XCuts.v290 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
