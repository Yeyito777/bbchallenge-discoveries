From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z119 XCuts.b119 XCuts.z120 XCuts.b120 XCuts.n119 XCuts.v119 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
