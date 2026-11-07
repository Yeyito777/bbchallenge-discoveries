From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z538 XCuts.b538 XCuts.z539 XCuts.b539 XCuts.n538 XCuts.v538 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
