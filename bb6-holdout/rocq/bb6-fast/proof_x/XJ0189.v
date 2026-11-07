From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z189 XCuts.b189 XCuts.z190 XCuts.b190 XCuts.n189 XCuts.v189 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
