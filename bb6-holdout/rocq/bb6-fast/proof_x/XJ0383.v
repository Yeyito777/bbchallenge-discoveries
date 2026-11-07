From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z383 XCuts.b383 XCuts.z384 XCuts.b384 XCuts.n383 XCuts.v383 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
