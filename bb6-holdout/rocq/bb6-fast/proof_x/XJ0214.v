From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z214 XCuts.b214 XCuts.z215 XCuts.b215 XCuts.n214 XCuts.v214 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
