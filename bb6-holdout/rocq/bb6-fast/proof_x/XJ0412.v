From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z412 XCuts.b412 XCuts.z413 XCuts.b413 XCuts.n412 XCuts.v412 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
