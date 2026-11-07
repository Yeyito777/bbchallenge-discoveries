From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z122 XCuts.b122 XCuts.z123 XCuts.b123 XCuts.n122 XCuts.v122 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
