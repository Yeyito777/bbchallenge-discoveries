From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z161 XCuts.b161 XCuts.z162 XCuts.b162 XCuts.n161 XCuts.v161 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
