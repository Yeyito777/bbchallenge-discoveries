From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z493 XCuts.b493 XCuts.z494 XCuts.b494 XCuts.n493 XCuts.v493 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
