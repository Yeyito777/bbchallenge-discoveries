From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z212 XCuts.b212 XCuts.z213 XCuts.b213 XCuts.n212 XCuts.v212 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
