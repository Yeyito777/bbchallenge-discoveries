From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z615 XCuts.b615 XCuts.z616 XCuts.b616 XCuts.n615 XCuts.v615 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
