From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z0 XCuts.b0 XCuts.z1 XCuts.b1 XCuts.n0 XCuts.v0 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
