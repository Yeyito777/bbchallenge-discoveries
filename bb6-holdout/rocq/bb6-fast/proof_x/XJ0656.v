From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z656 XCuts.b656 XCuts.z657 XCuts.b657 XCuts.n656 XCuts.v656 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
