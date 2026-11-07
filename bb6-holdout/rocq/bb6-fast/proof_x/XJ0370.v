From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z370 XCuts.b370 XCuts.z371 XCuts.b371 XCuts.n370 XCuts.v370 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
