From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z489 XCuts.b489 XCuts.z490 XCuts.b490 XCuts.n489 XCuts.v489 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
