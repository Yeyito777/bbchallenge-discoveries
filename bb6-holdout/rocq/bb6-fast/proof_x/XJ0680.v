From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z680 XCuts.b680 XCuts.z681 XCuts.b681 XCuts.n680 XCuts.v680 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
