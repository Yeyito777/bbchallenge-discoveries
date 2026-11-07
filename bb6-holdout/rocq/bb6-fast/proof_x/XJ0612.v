From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z612 XCuts.b612 XCuts.z613 XCuts.b613 XCuts.n612 XCuts.v612 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
