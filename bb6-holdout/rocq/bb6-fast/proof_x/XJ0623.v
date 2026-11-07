From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z623 XCuts.b623 XCuts.z624 XCuts.b624 XCuts.n623 XCuts.v623 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
