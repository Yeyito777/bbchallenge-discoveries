From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z589 XCuts.b589 XCuts.z590 XCuts.b590 XCuts.n589 XCuts.v589 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
