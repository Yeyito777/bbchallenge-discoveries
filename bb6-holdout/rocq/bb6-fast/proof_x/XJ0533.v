From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z533 XCuts.b533 XCuts.z534 XCuts.b534 XCuts.n533 XCuts.v533 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
