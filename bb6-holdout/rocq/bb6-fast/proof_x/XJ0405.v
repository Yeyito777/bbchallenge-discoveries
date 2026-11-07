From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z405 XCuts.b405 XCuts.z406 XCuts.b406 XCuts.n405 XCuts.v405 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
