From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z3 XCuts.b3 XCuts.z4 XCuts.b4 XCuts.n3 XCuts.v3 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
