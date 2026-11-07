From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z418 XCuts.b418 XCuts.z419 XCuts.b419 XCuts.n418 XCuts.v418 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
