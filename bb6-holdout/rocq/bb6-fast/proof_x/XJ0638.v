From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z638 XCuts.b638 XCuts.z639 XCuts.b639 XCuts.n638 XCuts.v638 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
