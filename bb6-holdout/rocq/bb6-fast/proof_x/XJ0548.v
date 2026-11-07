From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z548 XCuts.b548 XCuts.z549 XCuts.b549 XCuts.n548 XCuts.v548 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
