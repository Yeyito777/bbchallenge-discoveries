From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z365 XCuts.b365 XCuts.z366 XCuts.b366 XCuts.n365 XCuts.v365 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
