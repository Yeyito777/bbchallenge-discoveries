From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z641 XCuts.b641 XCuts.z642 XCuts.b642 XCuts.n641 XCuts.v641 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
