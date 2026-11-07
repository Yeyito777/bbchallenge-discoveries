From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z427 XCuts.b427 XCuts.z428 XCuts.b428 XCuts.n427 XCuts.v427 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
