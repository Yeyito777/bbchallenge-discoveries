From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z631 XCuts.b631 XCuts.z632 XCuts.b632 XCuts.n631 XCuts.v631 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
