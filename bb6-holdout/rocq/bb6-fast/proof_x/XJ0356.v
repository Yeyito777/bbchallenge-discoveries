From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z356 XCuts.b356 XCuts.z357 XCuts.b357 XCuts.n356 XCuts.v356 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
