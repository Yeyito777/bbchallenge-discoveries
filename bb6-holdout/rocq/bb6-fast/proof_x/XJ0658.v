From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z658 XCuts.b658 XCuts.z659 XCuts.b659 XCuts.n658 XCuts.v658 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
