From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z118 XCuts.b118 XCuts.z119 XCuts.b119 XCuts.n118 XCuts.v118 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
