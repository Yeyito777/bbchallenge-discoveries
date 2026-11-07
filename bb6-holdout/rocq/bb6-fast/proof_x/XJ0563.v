From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z563 XCuts.b563 XCuts.z564 XCuts.b564 XCuts.n563 XCuts.v563 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
