From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z384 XCuts.b384 XCuts.z385 XCuts.b385 XCuts.n384 XCuts.v384 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
