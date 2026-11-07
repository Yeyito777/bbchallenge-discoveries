From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z691 XCuts.b691 XCuts.z692 XCuts.b692 XCuts.n691 XCuts.v691 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
