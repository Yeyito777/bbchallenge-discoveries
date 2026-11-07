From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z627 XCuts.b627 XCuts.z628 XCuts.b628 XCuts.n627 XCuts.v627 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
