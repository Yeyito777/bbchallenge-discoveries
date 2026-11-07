From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z360 XCuts.b360 XCuts.z361 XCuts.b361 XCuts.n360 XCuts.v360 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
