From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z668 XCuts.b668 XCuts.z669 XCuts.b669 XCuts.n668 XCuts.v668 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
