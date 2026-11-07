From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z36 XCuts.b36 XCuts.z37 XCuts.b37 XCuts.n36 XCuts.v36 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
