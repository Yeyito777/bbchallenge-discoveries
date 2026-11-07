From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z87 XCuts.b87 XCuts.z88 XCuts.b88 XCuts.n87 XCuts.v87 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
