From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z643 XCuts.b643 XCuts.z644 XCuts.b644 XCuts.n643 XCuts.v643 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
