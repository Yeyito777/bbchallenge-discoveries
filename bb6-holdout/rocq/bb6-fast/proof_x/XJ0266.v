From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z266 XCuts.b266 XCuts.z267 XCuts.b267 XCuts.n266 XCuts.v266 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
