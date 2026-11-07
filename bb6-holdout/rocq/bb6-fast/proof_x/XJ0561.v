From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z561 XCuts.b561 XCuts.z562 XCuts.b562 XCuts.n561 XCuts.v561 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
