From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z7 XCuts.b7 XCuts.z8 XCuts.b8 XCuts.n7 XCuts.v7 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
