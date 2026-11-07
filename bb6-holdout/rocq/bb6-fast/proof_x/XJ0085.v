From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z85 XCuts.b85 XCuts.z86 XCuts.b86 XCuts.n85 XCuts.v85 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
