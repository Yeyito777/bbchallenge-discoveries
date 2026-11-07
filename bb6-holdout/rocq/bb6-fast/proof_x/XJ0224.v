From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z224 XCuts.b224 XCuts.z225 XCuts.b225 XCuts.n224 XCuts.v224 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
