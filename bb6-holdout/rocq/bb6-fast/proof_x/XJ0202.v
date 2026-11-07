From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z202 XCuts.b202 XCuts.z203 XCuts.b203 XCuts.n202 XCuts.v202 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
