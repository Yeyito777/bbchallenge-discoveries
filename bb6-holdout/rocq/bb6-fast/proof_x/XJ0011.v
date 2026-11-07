From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z11 XCuts.b11 XCuts.z12 XCuts.b12 XCuts.n11 XCuts.v11 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
