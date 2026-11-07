From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z389 XCuts.b389 XCuts.z390 XCuts.b390 XCuts.n389 XCuts.v389 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
