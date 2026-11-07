From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z134 XCuts.b134 XCuts.z135 XCuts.b135 XCuts.n134 XCuts.v134 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
