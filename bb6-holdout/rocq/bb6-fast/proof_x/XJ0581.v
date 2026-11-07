From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z581 XCuts.b581 XCuts.z582 XCuts.b582 XCuts.n581 XCuts.v581 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
