From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z654 XCuts.b654 XCuts.z655 XCuts.b655 XCuts.n654 XCuts.v654 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
