From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z379 XCuts.b379 XCuts.z380 XCuts.b380 XCuts.n379 XCuts.v379 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
