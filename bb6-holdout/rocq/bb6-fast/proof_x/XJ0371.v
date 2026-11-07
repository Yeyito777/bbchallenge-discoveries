From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z371 XCuts.b371 XCuts.z372 XCuts.b372 XCuts.n371 XCuts.v371 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
