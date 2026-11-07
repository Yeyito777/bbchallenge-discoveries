From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z346 XCuts.b346 XCuts.z347 XCuts.b347 XCuts.n346 XCuts.v346 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
