From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z485 XCuts.b485 XCuts.z486 XCuts.b486 XCuts.n485 XCuts.v485 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
