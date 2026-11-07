From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z473 XCuts.b473 XCuts.z474 XCuts.b474 XCuts.n473 XCuts.v473 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
