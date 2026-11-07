From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z172 XCuts.b172 XCuts.z173 XCuts.b173 XCuts.n172 XCuts.v172 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
