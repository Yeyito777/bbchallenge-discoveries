From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z439 XCuts.b439 XCuts.z440 XCuts.b440 XCuts.n439 XCuts.v439 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
