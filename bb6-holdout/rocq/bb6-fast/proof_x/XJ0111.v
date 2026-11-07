From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z111 XCuts.b111 XCuts.z112 XCuts.b112 XCuts.n111 XCuts.v111 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
