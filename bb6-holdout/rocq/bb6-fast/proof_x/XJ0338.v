From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z338 XCuts.b338 XCuts.z339 XCuts.b339 XCuts.n338 XCuts.v338 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
