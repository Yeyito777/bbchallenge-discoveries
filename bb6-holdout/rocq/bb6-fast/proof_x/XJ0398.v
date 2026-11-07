From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z398 XCuts.b398 XCuts.z399 XCuts.b399 XCuts.n398 XCuts.v398 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
