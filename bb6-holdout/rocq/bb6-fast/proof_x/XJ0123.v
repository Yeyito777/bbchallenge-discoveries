From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z123 XCuts.b123 XCuts.z124 XCuts.b124 XCuts.n123 XCuts.v123 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
