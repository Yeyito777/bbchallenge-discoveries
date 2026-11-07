From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z602 XCuts.b602 XCuts.z603 XCuts.b603 XCuts.n602 XCuts.v602 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
