From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z136 XCuts.b136 XCuts.z137 XCuts.b137 XCuts.n136 XCuts.v136 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
