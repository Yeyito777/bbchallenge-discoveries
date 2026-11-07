From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z128 XCuts.b128 XCuts.z129 XCuts.b129 XCuts.n128 XCuts.v128 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
