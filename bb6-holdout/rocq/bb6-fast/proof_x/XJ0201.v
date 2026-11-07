From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z201 XCuts.b201 XCuts.z202 XCuts.b202 XCuts.n201 XCuts.v201 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
