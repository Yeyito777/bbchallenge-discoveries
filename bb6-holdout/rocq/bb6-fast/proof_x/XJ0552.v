From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z552 XCuts.b552 XCuts.z553 XCuts.b553 XCuts.n552 XCuts.v552 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
