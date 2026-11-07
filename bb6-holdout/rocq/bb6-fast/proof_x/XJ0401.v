From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z401 XCuts.b401 XCuts.z402 XCuts.b402 XCuts.n401 XCuts.v401 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
