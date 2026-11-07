From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z540 XCuts.b540 XCuts.z541 XCuts.b541 XCuts.n540 XCuts.v540 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
