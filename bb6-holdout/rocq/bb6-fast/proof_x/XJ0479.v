From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z479 XCuts.b479 XCuts.z480 XCuts.b480 XCuts.n479 XCuts.v479 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
