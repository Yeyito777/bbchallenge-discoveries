From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z145 XCuts.b145 XCuts.z146 XCuts.b146 XCuts.n145 XCuts.v145 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
