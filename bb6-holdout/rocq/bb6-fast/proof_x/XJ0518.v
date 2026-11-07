From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z518 XCuts.b518 XCuts.z519 XCuts.b519 XCuts.n518 XCuts.v518 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
