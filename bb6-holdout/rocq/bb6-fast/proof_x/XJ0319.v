From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z319 XCuts.b319 XCuts.z320 XCuts.b320 XCuts.n319 XCuts.v319 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
