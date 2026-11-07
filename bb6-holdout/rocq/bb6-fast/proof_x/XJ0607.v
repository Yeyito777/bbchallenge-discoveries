From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z607 XCuts.b607 XCuts.z608 XCuts.b608 XCuts.n607 XCuts.v607 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
