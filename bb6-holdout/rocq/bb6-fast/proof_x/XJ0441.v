From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z441 XCuts.b441 XCuts.z442 XCuts.b442 XCuts.n441 XCuts.v441 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
