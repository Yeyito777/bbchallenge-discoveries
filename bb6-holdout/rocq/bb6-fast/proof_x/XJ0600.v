From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z600 XCuts.b600 XCuts.z601 XCuts.b601 XCuts.n600 XCuts.v600 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
