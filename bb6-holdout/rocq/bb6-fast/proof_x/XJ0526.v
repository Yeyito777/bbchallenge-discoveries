From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z526 XCuts.b526 XCuts.z527 XCuts.b527 XCuts.n526 XCuts.v526 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
