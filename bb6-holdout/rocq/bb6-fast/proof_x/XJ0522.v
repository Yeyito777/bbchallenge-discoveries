From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z522 XCuts.b522 XCuts.z523 XCuts.b523 XCuts.n522 XCuts.v522 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
