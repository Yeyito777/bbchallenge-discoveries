From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z124 XCuts.b124 XCuts.z125 XCuts.b125 XCuts.n124 XCuts.v124 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
