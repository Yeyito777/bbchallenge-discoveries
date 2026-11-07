From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z358 XCuts.b358 XCuts.z359 XCuts.b359 XCuts.n358 XCuts.v358 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
