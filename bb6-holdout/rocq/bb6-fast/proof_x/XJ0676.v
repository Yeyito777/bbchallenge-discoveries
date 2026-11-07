From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z676 XCuts.b676 XCuts.z677 XCuts.b677 XCuts.n676 XCuts.v676 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
