From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z438 XCuts.b438 XCuts.z439 XCuts.b439 XCuts.n438 XCuts.v438 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
