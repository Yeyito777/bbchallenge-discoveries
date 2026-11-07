From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z510 XCuts.b510 XCuts.z511 XCuts.b511 XCuts.n510 XCuts.v510 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
