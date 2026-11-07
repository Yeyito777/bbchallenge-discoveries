From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z167 XCuts.b167 XCuts.z168 XCuts.b168 XCuts.n167 XCuts.v167 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
