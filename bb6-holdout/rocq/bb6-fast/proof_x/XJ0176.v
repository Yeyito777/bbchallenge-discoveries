From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z176 XCuts.b176 XCuts.z177 XCuts.b177 XCuts.n176 XCuts.v176 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
