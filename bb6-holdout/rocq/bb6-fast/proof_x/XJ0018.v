From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z18 XCuts.b18 XCuts.z19 XCuts.b19 XCuts.n18 XCuts.v18 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
