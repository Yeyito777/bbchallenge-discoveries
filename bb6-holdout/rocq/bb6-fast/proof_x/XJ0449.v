From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z449 XCuts.b449 XCuts.z450 XCuts.b450 XCuts.n449 XCuts.v449 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
