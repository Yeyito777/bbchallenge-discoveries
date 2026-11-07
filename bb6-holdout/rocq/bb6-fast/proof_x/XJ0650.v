From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z650 XCuts.b650 XCuts.z651 XCuts.b651 XCuts.n650 XCuts.v650 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
