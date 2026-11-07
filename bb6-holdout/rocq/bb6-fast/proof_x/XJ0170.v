From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z170 XCuts.b170 XCuts.z171 XCuts.b171 XCuts.n170 XCuts.v170 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
