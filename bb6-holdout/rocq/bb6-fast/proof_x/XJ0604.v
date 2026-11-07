From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z604 XCuts.b604 XCuts.z605 XCuts.b605 XCuts.n604 XCuts.v604 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
