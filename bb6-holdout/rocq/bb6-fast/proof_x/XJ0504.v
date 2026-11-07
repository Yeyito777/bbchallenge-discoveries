From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z504 XCuts.b504 XCuts.z505 XCuts.b505 XCuts.n504 XCuts.v504 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
