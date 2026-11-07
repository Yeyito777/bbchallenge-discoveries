From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z261 XCuts.b261 XCuts.z262 XCuts.b262 XCuts.n261 XCuts.v261 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
