From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z608 XCuts.b608 XCuts.z609 XCuts.b609 XCuts.n608 XCuts.v608 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
