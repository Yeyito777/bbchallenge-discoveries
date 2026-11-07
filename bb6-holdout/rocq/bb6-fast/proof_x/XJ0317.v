From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z317 XCuts.b317 XCuts.z318 XCuts.b318 XCuts.n317 XCuts.v317 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
