From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z437 XCuts.b437 XCuts.z438 XCuts.b438 XCuts.n437 XCuts.v437 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
