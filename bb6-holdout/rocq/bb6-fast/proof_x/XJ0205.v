From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z205 XCuts.b205 XCuts.z206 XCuts.b206 XCuts.n205 XCuts.v205 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
