From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z155 XCuts.b155 XCuts.z156 XCuts.b156 XCuts.n155 XCuts.v155 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
