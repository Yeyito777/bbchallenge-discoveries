From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z619 XCuts.b619 XCuts.z620 XCuts.b620 XCuts.n619 XCuts.v619 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
