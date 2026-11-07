From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z101 XCuts.b101 XCuts.z102 XCuts.b102 XCuts.n101 XCuts.v101 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
