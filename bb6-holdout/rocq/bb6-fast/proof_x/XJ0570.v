From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z570 XCuts.b570 XCuts.z571 XCuts.b571 XCuts.n570 XCuts.v570 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
