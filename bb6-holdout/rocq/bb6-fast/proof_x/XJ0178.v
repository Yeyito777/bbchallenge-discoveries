From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z178 XCuts.b178 XCuts.z179 XCuts.b179 XCuts.n178 XCuts.v178 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
