From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z344 XCuts.b344 XCuts.z345 XCuts.b345 XCuts.n344 XCuts.v344 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
