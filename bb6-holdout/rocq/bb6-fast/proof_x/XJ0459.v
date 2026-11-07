From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z459 XCuts.b459 XCuts.z460 XCuts.b460 XCuts.n459 XCuts.v459 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
