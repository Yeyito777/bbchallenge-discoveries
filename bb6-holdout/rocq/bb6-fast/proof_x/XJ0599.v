From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z599 XCuts.b599 XCuts.z600 XCuts.b600 XCuts.n599 XCuts.v599 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
