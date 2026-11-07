From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z99 XCuts.b99 XCuts.z100 XCuts.b100 XCuts.n99 XCuts.v99 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
