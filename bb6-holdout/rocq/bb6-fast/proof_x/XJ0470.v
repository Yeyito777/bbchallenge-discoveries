From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z470 XCuts.b470 XCuts.z471 XCuts.b471 XCuts.n470 XCuts.v470 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
