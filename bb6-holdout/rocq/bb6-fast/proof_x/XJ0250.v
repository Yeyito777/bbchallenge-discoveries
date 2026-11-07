From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z250 XCuts.b250 XCuts.z251 XCuts.b251 XCuts.n250 XCuts.v250 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
