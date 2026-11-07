From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z625 XCuts.b625 XCuts.z626 XCuts.b626 XCuts.n625 XCuts.v625 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
