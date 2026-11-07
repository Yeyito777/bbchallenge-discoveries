From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z486 XCuts.b486 XCuts.z487 XCuts.b487 XCuts.n486 XCuts.v486 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
