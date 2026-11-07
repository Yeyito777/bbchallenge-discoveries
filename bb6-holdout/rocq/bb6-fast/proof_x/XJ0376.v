From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z376 XCuts.b376 XCuts.z377 XCuts.b377 XCuts.n376 XCuts.v376 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
