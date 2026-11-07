From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z630 XCuts.b630 XCuts.z631 XCuts.b631 XCuts.n630 XCuts.v630 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
