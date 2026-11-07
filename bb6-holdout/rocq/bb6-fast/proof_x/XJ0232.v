From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z232 XCuts.b232 XCuts.z233 XCuts.b233 XCuts.n232 XCuts.v232 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
