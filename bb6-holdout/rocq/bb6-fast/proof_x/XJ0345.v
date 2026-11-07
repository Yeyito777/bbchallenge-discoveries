From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z345 XCuts.b345 XCuts.z346 XCuts.b346 XCuts.n345 XCuts.v345 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
