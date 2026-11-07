From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z35 XCuts.b35 XCuts.z36 XCuts.b36 XCuts.n35 XCuts.v35 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
