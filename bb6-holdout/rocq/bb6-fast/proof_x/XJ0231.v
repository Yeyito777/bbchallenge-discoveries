From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z231 XCuts.b231 XCuts.z232 XCuts.b232 XCuts.n231 XCuts.v231 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
