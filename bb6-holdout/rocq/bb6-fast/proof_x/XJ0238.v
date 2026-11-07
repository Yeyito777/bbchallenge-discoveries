From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z238 XCuts.b238 XCuts.z239 XCuts.b239 XCuts.n238 XCuts.v238 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
