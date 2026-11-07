From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z217 XCuts.b217 XCuts.z218 XCuts.b218 XCuts.n217 XCuts.v217 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
