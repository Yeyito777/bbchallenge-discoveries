From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z632 XCuts.b632 XCuts.z633 XCuts.b633 XCuts.n632 XCuts.v632 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
