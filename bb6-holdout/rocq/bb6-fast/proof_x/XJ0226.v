From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z226 XCuts.b226 XCuts.z227 XCuts.b227 XCuts.n226 XCuts.v226 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
