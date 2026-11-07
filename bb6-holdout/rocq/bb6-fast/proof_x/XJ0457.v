From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z457 XCuts.b457 XCuts.z458 XCuts.b458 XCuts.n457 XCuts.v457 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
