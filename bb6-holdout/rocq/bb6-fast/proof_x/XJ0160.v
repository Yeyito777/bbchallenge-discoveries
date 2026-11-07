From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z160 XCuts.b160 XCuts.z161 XCuts.b161 XCuts.n160 XCuts.v160 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
