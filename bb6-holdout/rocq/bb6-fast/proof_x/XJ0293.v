From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z293 XCuts.b293 XCuts.z294 XCuts.b294 XCuts.n293 XCuts.v293 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
