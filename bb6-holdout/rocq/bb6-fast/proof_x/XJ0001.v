From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z1 XCuts.b1 XCuts.z2 XCuts.b2 XCuts.n1 XCuts.v1 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
