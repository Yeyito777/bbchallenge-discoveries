From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z626 XCuts.b626 XCuts.z627 XCuts.b627 XCuts.n626 XCuts.v626 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
