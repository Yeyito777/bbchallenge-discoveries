From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z456 XCuts.b456 XCuts.z457 XCuts.b457 XCuts.n456 XCuts.v456 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
