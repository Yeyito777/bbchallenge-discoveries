From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z30 XCuts.b30 XCuts.z31 XCuts.b31 XCuts.n30 XCuts.v30 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
