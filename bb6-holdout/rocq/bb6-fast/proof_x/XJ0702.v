From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z702 XCuts.b702 XCuts.z703 XCuts.b703 XCuts.n702 XCuts.v702 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
