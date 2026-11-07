From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z252 XCuts.b252 XCuts.z253 XCuts.b253 XCuts.n252 XCuts.v252 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
