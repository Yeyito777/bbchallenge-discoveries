From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z382 XCuts.b382 XCuts.z383 XCuts.b383 XCuts.n382 XCuts.v382 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
