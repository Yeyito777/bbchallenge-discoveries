From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z642 XCuts.b642 XCuts.z643 XCuts.b643 XCuts.n642 XCuts.v642 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
