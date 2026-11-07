From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z336 XCuts.b336 XCuts.z337 XCuts.b337 XCuts.n336 XCuts.v336 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
