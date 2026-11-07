From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z415 XCuts.b415 XCuts.z416 XCuts.b416 XCuts.n415 XCuts.v415 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
