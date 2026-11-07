From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z343 XCuts.b343 XCuts.z344 XCuts.b344 XCuts.n343 XCuts.v343 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
