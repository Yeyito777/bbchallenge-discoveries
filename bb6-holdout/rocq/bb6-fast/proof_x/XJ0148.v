From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z148 XCuts.b148 XCuts.z149 XCuts.b149 XCuts.n148 XCuts.v148 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
