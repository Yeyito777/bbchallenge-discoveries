From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z308 XCuts.b308 XCuts.z309 XCuts.b309 XCuts.n308 XCuts.v308 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
