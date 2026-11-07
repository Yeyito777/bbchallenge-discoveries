From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z669 XCuts.b669 XCuts.z670 XCuts.b670 XCuts.n669 XCuts.v669 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
