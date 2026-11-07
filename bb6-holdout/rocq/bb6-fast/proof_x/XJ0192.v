From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z192 XCuts.b192 XCuts.z193 XCuts.b193 XCuts.n192 XCuts.v192 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
