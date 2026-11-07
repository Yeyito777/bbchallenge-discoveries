From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z536 XCuts.b536 XCuts.z537 XCuts.b537 XCuts.n536 XCuts.v536 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
