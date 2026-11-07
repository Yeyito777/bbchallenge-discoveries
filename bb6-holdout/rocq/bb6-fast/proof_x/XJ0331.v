From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z331 XCuts.b331 XCuts.z332 XCuts.b332 XCuts.n331 XCuts.v331 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
