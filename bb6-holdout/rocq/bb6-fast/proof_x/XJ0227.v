From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z227 XCuts.b227 XCuts.z228 XCuts.b228 XCuts.n227 XCuts.v227 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
