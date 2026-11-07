From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z571 XCuts.b571 XCuts.z572 XCuts.b572 XCuts.n571 XCuts.v571 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
