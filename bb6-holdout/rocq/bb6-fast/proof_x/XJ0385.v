From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z385 XCuts.b385 XCuts.z386 XCuts.b386 XCuts.n385 XCuts.v385 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
