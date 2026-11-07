From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z173 XCuts.b173 XCuts.z174 XCuts.b174 XCuts.n173 XCuts.v173 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
