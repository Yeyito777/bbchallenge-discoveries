From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z496 XCuts.b496 XCuts.z497 XCuts.b497 XCuts.n496 XCuts.v496 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
