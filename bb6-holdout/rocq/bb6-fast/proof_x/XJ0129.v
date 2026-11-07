From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z129 XCuts.b129 XCuts.z130 XCuts.b130 XCuts.n129 XCuts.v129 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
