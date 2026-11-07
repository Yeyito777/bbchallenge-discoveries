From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z359 XCuts.b359 XCuts.z360 XCuts.b360 XCuts.n359 XCuts.v359 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
