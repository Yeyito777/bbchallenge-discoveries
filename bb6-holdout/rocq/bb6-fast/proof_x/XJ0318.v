From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z318 XCuts.b318 XCuts.z319 XCuts.b319 XCuts.n318 XCuts.v318 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
