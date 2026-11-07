From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z690 XCuts.b690 XCuts.z691 XCuts.b691 XCuts.n690 XCuts.v690 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
