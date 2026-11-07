From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z408 XCuts.b408 XCuts.z409 XCuts.b409 XCuts.n408 XCuts.v408 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
