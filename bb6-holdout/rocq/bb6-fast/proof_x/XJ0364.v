From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z364 XCuts.b364 XCuts.z365 XCuts.b365 XCuts.n364 XCuts.v364 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
