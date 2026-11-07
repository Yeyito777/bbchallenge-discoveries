From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z397 XCuts.b397 XCuts.z398 XCuts.b398 XCuts.n397 XCuts.v397 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
