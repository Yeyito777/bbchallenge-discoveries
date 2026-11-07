From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z590 XCuts.b590 XCuts.z591 XCuts.b591 XCuts.n590 XCuts.v590 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
