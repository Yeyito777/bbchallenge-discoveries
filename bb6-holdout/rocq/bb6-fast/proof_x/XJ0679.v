From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z679 XCuts.b679 XCuts.z680 XCuts.b680 XCuts.n679 XCuts.v679 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
