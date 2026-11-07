From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z503 XCuts.b503 XCuts.z504 XCuts.b504 XCuts.n503 XCuts.v503 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
