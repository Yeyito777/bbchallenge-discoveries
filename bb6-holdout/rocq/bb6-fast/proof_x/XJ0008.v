From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z8 XCuts.b8 XCuts.z9 XCuts.b9 XCuts.n8 XCuts.v8 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
