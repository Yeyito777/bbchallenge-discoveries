From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z532 XCuts.b532 XCuts.z533 XCuts.b533 XCuts.n532 XCuts.v532 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
