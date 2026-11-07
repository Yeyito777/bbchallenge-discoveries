From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z235 XCuts.b235 XCuts.z236 XCuts.b236 XCuts.n235 XCuts.v235 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
