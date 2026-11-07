From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z511 XCuts.b511 XCuts.z512 XCuts.b512 XCuts.n511 XCuts.v511 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
