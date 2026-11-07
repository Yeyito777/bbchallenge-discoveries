From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z133 XCuts.b133 XCuts.z134 XCuts.b134 XCuts.n133 XCuts.v133 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
