From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z440 XCuts.b440 XCuts.z441 XCuts.b441 XCuts.n440 XCuts.v440 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
