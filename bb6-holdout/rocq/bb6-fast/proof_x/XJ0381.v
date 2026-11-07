From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z381 XCuts.b381 XCuts.z382 XCuts.b382 XCuts.n381 XCuts.v381 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
