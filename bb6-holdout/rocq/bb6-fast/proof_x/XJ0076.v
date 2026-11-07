From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z76 XCuts.b76 XCuts.z77 XCuts.b77 XCuts.n76 XCuts.v76 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
