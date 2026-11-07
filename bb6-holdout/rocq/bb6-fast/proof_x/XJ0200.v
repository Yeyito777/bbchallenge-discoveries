From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z200 XCuts.b200 XCuts.z201 XCuts.b201 XCuts.n200 XCuts.v200 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
