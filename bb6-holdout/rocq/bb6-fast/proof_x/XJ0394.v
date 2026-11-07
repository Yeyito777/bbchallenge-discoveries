From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z394 XCuts.b394 XCuts.z395 XCuts.b395 XCuts.n394 XCuts.v394 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
