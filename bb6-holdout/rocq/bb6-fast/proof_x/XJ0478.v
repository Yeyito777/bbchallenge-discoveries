From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z478 XCuts.b478 XCuts.z479 XCuts.b479 XCuts.n478 XCuts.v478 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
