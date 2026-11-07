From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z666 XCuts.b666 XCuts.z667 XCuts.b667 XCuts.n666 XCuts.v666 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
