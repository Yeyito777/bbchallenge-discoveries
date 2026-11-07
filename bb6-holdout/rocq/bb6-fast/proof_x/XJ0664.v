From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z664 XCuts.b664 XCuts.z665 XCuts.b665 XCuts.n664 XCuts.v664 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
