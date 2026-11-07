From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z525 XCuts.b525 XCuts.z526 XCuts.b526 XCuts.n525 XCuts.v525 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
