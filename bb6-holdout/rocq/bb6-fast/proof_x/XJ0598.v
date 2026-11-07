From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z598 XCuts.b598 XCuts.z599 XCuts.b599 XCuts.n598 XCuts.v598 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
