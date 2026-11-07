From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z565 XCuts.b565 XCuts.z566 XCuts.b566 XCuts.n565 XCuts.v565 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
