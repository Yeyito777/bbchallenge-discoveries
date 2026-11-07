From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z372 XCuts.b372 XCuts.z373 XCuts.b373 XCuts.n372 XCuts.v372 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
