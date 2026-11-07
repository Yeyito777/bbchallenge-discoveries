From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z83 XCuts.b83 XCuts.z84 XCuts.b84 XCuts.n83 XCuts.v83 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
