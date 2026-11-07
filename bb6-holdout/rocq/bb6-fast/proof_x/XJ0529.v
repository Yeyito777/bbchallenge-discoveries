From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z529 XCuts.b529 XCuts.z530 XCuts.b530 XCuts.n529 XCuts.v529 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
