From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z102 XCuts.b102 XCuts.z103 XCuts.b103 XCuts.n102 XCuts.v102 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
