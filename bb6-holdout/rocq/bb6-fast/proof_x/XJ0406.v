From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z406 XCuts.b406 XCuts.z407 XCuts.b407 XCuts.n406 XCuts.v406 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
