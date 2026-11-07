From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z324 XCuts.b324 XCuts.z325 XCuts.b325 XCuts.n324 XCuts.v324 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
