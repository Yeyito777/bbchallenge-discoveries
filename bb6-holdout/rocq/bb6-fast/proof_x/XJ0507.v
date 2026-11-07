From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z507 XCuts.b507 XCuts.z508 XCuts.b508 XCuts.n507 XCuts.v507 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
