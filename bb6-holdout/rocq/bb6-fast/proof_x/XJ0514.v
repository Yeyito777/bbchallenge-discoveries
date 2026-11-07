From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z514 XCuts.b514 XCuts.z515 XCuts.b515 XCuts.n514 XCuts.v514 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
