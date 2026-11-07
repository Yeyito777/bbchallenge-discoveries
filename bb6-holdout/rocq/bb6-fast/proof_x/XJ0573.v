From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z573 XCuts.b573 XCuts.z574 XCuts.b574 XCuts.n573 XCuts.v573 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
