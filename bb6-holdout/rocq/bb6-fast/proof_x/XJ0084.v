From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z84 XCuts.b84 XCuts.z85 XCuts.b85 XCuts.n84 XCuts.v84 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
