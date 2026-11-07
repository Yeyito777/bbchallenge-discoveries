From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z665 XCuts.b665 XCuts.z666 XCuts.b666 XCuts.n665 XCuts.v665 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
