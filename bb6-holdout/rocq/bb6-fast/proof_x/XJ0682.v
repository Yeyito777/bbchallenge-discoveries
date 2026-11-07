From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z682 XCuts.b682 XCuts.z683 XCuts.b683 XCuts.n682 XCuts.v682 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
