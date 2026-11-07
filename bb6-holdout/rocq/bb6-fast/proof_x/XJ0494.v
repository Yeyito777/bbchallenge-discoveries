From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z494 XCuts.b494 XCuts.z495 XCuts.b495 XCuts.n494 XCuts.v494 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
