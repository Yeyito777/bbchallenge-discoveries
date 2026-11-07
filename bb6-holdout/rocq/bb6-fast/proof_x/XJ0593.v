From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z593 XCuts.b593 XCuts.z594 XCuts.b594 XCuts.n593 XCuts.v593 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
