From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z460 XCuts.b460 XCuts.z461 XCuts.b461 XCuts.n460 XCuts.v460 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
