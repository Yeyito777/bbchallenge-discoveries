From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z188 XCuts.b188 XCuts.z189 XCuts.b189 XCuts.n188 XCuts.v188 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
