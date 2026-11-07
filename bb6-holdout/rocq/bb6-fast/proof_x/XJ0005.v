From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z5 XCuts.b5 XCuts.z6 XCuts.b6 XCuts.n5 XCuts.v5 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
