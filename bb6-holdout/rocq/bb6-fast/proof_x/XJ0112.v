From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z112 XCuts.b112 XCuts.z113 XCuts.b113 XCuts.n112 XCuts.v112 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
