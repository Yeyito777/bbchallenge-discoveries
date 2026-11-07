From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z80 XCuts.b80 XCuts.z81 XCuts.b81 XCuts.n80 XCuts.v80 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
