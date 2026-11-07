From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z448 XCuts.b448 XCuts.z449 XCuts.b449 XCuts.n448 XCuts.v448 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
