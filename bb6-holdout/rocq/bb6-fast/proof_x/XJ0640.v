From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z640 XCuts.b640 XCuts.z641 XCuts.b641 XCuts.n640 XCuts.v640 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
