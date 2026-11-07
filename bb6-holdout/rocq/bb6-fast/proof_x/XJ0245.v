From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z245 XCuts.b245 XCuts.z246 XCuts.b246 XCuts.n245 XCuts.v245 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
