From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z352 XCuts.b352 XCuts.z353 XCuts.b353 XCuts.n352 XCuts.v352 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
