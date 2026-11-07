From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z560 XCuts.b560 XCuts.z561 XCuts.b561 XCuts.n560 XCuts.v560 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
