From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z234 XCuts.b234 XCuts.z235 XCuts.b235 XCuts.n234 XCuts.v234 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
