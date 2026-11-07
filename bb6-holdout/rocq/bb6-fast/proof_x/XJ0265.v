From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z265 XCuts.b265 XCuts.z266 XCuts.b266 XCuts.n265 XCuts.v265 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
