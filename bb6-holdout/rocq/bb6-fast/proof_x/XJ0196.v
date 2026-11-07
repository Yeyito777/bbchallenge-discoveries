From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z196 XCuts.b196 XCuts.z197 XCuts.b197 XCuts.n196 XCuts.v196 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
