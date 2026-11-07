From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z378 XCuts.b378 XCuts.z379 XCuts.b379 XCuts.n378 XCuts.v378 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
