From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z46 XCuts.b46 XCuts.z47 XCuts.b47 XCuts.n46 XCuts.v46 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
