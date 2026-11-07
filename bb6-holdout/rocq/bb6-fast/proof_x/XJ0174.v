From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z174 XCuts.b174 XCuts.z175 XCuts.b175 XCuts.n174 XCuts.v174 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
