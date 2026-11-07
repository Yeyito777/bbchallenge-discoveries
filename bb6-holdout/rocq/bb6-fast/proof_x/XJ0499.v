From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z499 XCuts.b499 XCuts.z500 XCuts.b500 XCuts.n499 XCuts.v499 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
