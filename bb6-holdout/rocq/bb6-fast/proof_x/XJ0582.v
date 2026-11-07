From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z582 XCuts.b582 XCuts.z583 XCuts.b583 XCuts.n582 XCuts.v582 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
