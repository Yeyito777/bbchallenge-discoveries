From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z246 XCuts.b246 XCuts.z247 XCuts.b247 XCuts.n246 XCuts.v246 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
