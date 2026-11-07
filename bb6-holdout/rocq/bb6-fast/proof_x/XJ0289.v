From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z289 XCuts.b289 XCuts.z290 XCuts.b290 XCuts.n289 XCuts.v289 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
