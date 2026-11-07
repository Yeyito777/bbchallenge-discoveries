From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z606 XCuts.b606 XCuts.z607 XCuts.b607 XCuts.n606 XCuts.v606 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
