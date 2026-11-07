From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z197 XCuts.b197 XCuts.z198 XCuts.b198 XCuts.n197 XCuts.v197 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
