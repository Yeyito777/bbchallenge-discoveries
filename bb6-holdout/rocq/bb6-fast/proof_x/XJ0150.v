From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z150 XCuts.b150 XCuts.z151 XCuts.b151 XCuts.n150 XCuts.v150 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
