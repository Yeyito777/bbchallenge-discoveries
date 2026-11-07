From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z337 XCuts.b337 XCuts.z338 XCuts.b338 XCuts.n337 XCuts.v337 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
