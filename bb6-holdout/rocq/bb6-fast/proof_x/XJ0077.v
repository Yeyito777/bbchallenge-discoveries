From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z77 XCuts.b77 XCuts.z78 XCuts.b78 XCuts.n77 XCuts.v77 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
