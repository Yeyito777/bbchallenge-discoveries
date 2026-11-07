From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z333 XCuts.b333 XCuts.z334 XCuts.b334 XCuts.n333 XCuts.v333 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
