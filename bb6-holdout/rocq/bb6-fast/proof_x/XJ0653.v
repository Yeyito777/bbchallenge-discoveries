From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z653 XCuts.b653 XCuts.z654 XCuts.b654 XCuts.n653 XCuts.v653 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
