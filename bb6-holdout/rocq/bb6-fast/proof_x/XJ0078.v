From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z78 XCuts.b78 XCuts.z79 XCuts.b79 XCuts.n78 XCuts.v78 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
