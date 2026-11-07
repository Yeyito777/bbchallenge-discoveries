From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z253 XCuts.b253 XCuts.z254 XCuts.b254 XCuts.n253 XCuts.v253 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
