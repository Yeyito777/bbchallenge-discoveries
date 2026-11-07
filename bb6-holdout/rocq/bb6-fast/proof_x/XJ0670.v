From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z670 XCuts.b670 XCuts.z671 XCuts.b671 XCuts.n670 XCuts.v670 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
