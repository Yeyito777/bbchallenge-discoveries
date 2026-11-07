From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z100 XCuts.b100 XCuts.z101 XCuts.b101 XCuts.n100 XCuts.v100 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
