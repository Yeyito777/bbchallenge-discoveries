From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z17 XCuts.b17 XCuts.z18 XCuts.b18 XCuts.n17 XCuts.v17 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
