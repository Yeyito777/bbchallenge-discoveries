From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z541 XCuts.b541 XCuts.z542 XCuts.b542 XCuts.n541 XCuts.v541 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
