From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z230 XCuts.b230 XCuts.z231 XCuts.b231 XCuts.n230 XCuts.v230 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
