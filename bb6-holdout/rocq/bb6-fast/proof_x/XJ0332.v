From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z332 XCuts.b332 XCuts.z333 XCuts.b333 XCuts.n332 XCuts.v332 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
