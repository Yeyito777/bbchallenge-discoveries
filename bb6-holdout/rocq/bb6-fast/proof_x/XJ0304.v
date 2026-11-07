From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z304 XCuts.b304 XCuts.z305 XCuts.b305 XCuts.n304 XCuts.v304 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
