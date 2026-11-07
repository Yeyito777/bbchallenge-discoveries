From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z357 XCuts.b357 XCuts.z358 XCuts.b358 XCuts.n357 XCuts.v357 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
