From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z298 XCuts.b298 XCuts.z299 XCuts.b299 XCuts.n298 XCuts.v298 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
