From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z179 XCuts.b179 XCuts.z180 XCuts.b180 XCuts.n179 XCuts.v179 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
