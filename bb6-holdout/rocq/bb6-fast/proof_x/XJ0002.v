From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z2 XCuts.b2 XCuts.z3 XCuts.b3 XCuts.n2 XCuts.v2 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
