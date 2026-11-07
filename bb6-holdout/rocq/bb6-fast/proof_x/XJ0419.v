From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z419 XCuts.b419 XCuts.z420 XCuts.b420 XCuts.n419 XCuts.v419 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
