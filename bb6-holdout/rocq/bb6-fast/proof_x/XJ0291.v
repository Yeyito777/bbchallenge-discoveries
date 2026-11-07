From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z291 XCuts.b291 XCuts.z292 XCuts.b292 XCuts.n291 XCuts.v291 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
