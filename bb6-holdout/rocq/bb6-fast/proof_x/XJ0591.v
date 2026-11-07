From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z591 XCuts.b591 XCuts.z592 XCuts.b592 XCuts.n591 XCuts.v591 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
