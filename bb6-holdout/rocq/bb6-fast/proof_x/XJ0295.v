From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z295 XCuts.b295 XCuts.z296 XCuts.b296 XCuts.n295 XCuts.v295 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
