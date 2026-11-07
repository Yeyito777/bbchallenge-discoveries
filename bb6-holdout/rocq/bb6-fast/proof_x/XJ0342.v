From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z342 XCuts.b342 XCuts.z343 XCuts.b343 XCuts.n342 XCuts.v342 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
