From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z193 XCuts.b193 XCuts.z194 XCuts.b194 XCuts.n193 XCuts.v193 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
