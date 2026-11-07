From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z677 XCuts.b677 XCuts.z678 XCuts.b678 XCuts.n677 XCuts.v677 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
