From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z487 XCuts.b487 XCuts.z488 XCuts.b488 XCuts.n487 XCuts.v487 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
