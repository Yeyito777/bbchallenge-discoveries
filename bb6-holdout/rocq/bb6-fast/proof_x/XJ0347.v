From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z347 XCuts.b347 XCuts.z348 XCuts.b348 XCuts.n347 XCuts.v347 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
