From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z375 XCuts.b375 XCuts.z376 XCuts.b376 XCuts.n375 XCuts.v375 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
