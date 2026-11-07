From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z166 XCuts.b166 XCuts.z167 XCuts.b167 XCuts.n166 XCuts.v166 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
