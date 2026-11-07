From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z495 XCuts.b495 XCuts.z496 XCuts.b496 XCuts.n495 XCuts.v495 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
