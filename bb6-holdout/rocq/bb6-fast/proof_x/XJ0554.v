From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z554 XCuts.b554 XCuts.z555 XCuts.b555 XCuts.n554 XCuts.v554 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
