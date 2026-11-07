From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z505 XCuts.b505 XCuts.z506 XCuts.b506 XCuts.n505 XCuts.v505 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
