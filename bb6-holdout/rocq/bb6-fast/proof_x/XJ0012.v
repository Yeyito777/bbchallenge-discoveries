From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z12 XCuts.b12 XCuts.z13 XCuts.b13 XCuts.n12 XCuts.v12 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
