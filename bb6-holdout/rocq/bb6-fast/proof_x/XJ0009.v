From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z9 XCuts.b9 XCuts.z10 XCuts.b10 XCuts.n9 XCuts.v9 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
