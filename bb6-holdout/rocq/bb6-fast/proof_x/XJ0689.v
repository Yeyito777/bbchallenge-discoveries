From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z689 XCuts.b689 XCuts.z690 XCuts.b690 XCuts.n689 XCuts.v689 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
