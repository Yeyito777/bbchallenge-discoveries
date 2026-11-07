From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z472 XCuts.b472 XCuts.z473 XCuts.b473 XCuts.n472 XCuts.v472 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
