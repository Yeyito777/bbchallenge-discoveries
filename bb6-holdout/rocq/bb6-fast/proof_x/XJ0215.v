From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z215 XCuts.b215 XCuts.z216 XCuts.b216 XCuts.n215 XCuts.v215 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
