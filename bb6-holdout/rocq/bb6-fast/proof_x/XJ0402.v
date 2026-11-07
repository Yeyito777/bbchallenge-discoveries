From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z402 XCuts.b402 XCuts.z403 XCuts.b403 XCuts.n402 XCuts.v402 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
