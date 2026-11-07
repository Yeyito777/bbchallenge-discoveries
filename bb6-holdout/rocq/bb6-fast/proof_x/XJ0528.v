From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z528 XCuts.b528 XCuts.z529 XCuts.b529 XCuts.n528 XCuts.v528 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
