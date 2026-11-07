From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z4 XCuts.b4 XCuts.z5 XCuts.b5 XCuts.n4 XCuts.v4 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
