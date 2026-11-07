From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z699 XCuts.b699 XCuts.z700 XCuts.b700 XCuts.n699 XCuts.v699 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
