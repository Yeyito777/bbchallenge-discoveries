From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z580 XCuts.b580 XCuts.z581 XCuts.b581 XCuts.n580 XCuts.v580 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
