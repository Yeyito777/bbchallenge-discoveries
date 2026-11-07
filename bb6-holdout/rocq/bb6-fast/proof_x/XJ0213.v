From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z213 XCuts.b213 XCuts.z214 XCuts.b214 XCuts.n213 XCuts.v213 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
