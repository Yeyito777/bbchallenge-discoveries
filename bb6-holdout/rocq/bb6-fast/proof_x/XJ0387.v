From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z387 XCuts.b387 XCuts.z388 XCuts.b388 XCuts.n387 XCuts.v387 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
