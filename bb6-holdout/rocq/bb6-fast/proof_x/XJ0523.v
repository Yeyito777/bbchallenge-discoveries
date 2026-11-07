From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z523 XCuts.b523 XCuts.z524 XCuts.b524 XCuts.n523 XCuts.v523 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
