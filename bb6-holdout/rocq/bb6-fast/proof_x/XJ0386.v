From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z386 XCuts.b386 XCuts.z387 XCuts.b387 XCuts.n386 XCuts.v386 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
