From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z622 XCuts.b622 XCuts.z623 XCuts.b623 XCuts.n622 XCuts.v622 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
