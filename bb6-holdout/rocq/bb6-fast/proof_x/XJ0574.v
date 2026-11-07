From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z574 XCuts.b574 XCuts.z575 XCuts.b575 XCuts.n574 XCuts.v574 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
