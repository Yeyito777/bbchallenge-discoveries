From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z10 XCuts.b10 XCuts.z11 XCuts.b11 XCuts.n10 XCuts.v10 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
