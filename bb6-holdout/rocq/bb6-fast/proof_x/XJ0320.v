From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z320 XCuts.b320 XCuts.z321 XCuts.b321 XCuts.n320 XCuts.v320 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
