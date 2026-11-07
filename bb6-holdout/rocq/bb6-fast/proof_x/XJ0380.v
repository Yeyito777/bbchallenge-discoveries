From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z380 XCuts.b380 XCuts.z381 XCuts.b381 XCuts.n380 XCuts.v380 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
