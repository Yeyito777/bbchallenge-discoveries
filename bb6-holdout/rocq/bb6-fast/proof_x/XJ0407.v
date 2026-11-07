From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z407 XCuts.b407 XCuts.z408 XCuts.b408 XCuts.n407 XCuts.v407 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
