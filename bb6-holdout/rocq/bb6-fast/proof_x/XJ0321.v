From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z321 XCuts.b321 XCuts.z322 XCuts.b322 XCuts.n321 XCuts.v321 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
