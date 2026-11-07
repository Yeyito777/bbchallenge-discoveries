From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z404 XCuts.b404 XCuts.z405 XCuts.b405 XCuts.n404 XCuts.v404 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
