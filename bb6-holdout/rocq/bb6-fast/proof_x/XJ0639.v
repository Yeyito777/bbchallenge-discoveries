From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z639 XCuts.b639 XCuts.z640 XCuts.b640 XCuts.n639 XCuts.v639 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
