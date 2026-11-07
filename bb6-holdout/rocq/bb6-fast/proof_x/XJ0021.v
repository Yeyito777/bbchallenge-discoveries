From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z21 XCuts.b21 XCuts.z22 XCuts.b22 XCuts.n21 XCuts.v21 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
