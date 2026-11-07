From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z146 XCuts.b146 XCuts.z147 XCuts.b147 XCuts.n146 XCuts.v146 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
