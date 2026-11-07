From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z108 XCuts.b108 XCuts.z109 XCuts.b109 XCuts.n108 XCuts.v108 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
