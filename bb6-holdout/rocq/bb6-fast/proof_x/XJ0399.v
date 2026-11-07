From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z399 XCuts.b399 XCuts.z400 XCuts.b400 XCuts.n399 XCuts.v399 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
