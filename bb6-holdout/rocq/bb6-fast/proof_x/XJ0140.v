From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z140 XCuts.b140 XCuts.z141 XCuts.b141 XCuts.n140 XCuts.v140 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
