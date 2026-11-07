From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z396 XCuts.b396 XCuts.z397 XCuts.b397 XCuts.n396 XCuts.v396 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
