From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z22 XCuts.b22 XCuts.z23 XCuts.b23 XCuts.n22 XCuts.v22 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
