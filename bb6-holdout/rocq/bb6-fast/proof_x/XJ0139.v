From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z139 XCuts.b139 XCuts.z140 XCuts.b140 XCuts.n139 XCuts.v139 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
