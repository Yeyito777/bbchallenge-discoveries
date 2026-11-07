From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z461 XCuts.b461 XCuts.z462 XCuts.b462 XCuts.n461 XCuts.v461 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
