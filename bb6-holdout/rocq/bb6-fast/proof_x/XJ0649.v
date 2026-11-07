From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z649 XCuts.b649 XCuts.z650 XCuts.b650 XCuts.n649 XCuts.v649 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
