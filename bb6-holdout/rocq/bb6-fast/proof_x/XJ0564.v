From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z564 XCuts.b564 XCuts.z565 XCuts.b565 XCuts.n564 XCuts.v564 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
