From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z47 XCuts.b47 XCuts.z48 XCuts.b48 XCuts.n47 XCuts.v47 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
