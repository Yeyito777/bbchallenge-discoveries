From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z94 XCuts.b94 XCuts.z95 XCuts.b95 XCuts.n94 XCuts.v94 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
