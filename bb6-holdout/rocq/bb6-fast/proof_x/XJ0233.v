From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z233 XCuts.b233 XCuts.z234 XCuts.b234 XCuts.n233 XCuts.v233 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
