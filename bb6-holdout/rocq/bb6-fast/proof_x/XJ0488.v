From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z488 XCuts.b488 XCuts.z489 XCuts.b489 XCuts.n488 XCuts.v488 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
