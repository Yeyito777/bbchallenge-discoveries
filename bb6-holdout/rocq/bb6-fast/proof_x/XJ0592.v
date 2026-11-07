From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z592 XCuts.b592 XCuts.z593 XCuts.b593 XCuts.n592 XCuts.v592 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
