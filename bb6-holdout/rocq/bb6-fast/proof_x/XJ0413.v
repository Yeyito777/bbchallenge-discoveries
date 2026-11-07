From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z413 XCuts.b413 XCuts.z414 XCuts.b414 XCuts.n413 XCuts.v413 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
