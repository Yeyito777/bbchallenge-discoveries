From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z14 XCuts.b14 XCuts.z15 XCuts.b15 XCuts.n14 XCuts.v14 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
