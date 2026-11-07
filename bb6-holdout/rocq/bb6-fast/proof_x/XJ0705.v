From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z705 XCuts.b705 XCuts.z706 XCuts.b706 XCuts.n705 XCuts.v705 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
