From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z675 XCuts.b675 XCuts.z676 XCuts.b676 XCuts.n675 XCuts.v675 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
