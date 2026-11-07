From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z79 XCuts.b79 XCuts.z80 XCuts.b80 XCuts.n79 XCuts.v79 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
