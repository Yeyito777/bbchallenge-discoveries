From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z51 XCuts.b51 XCuts.z52 XCuts.b52 XCuts.n51 XCuts.v51 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
