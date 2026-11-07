From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z260 XCuts.b260 XCuts.z261 XCuts.b261 XCuts.n260 XCuts.v260 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
