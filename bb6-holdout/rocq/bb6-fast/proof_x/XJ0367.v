From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z367 XCuts.b367 XCuts.z368 XCuts.b368 XCuts.n367 XCuts.v367 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
