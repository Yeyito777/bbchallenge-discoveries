From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z390 XCuts.b390 XCuts.z391 XCuts.b391 XCuts.n390 XCuts.v390 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
