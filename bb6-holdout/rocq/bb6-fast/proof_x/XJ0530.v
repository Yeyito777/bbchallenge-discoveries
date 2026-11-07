From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z530 XCuts.b530 XCuts.z531 XCuts.b531 XCuts.n530 XCuts.v530 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
