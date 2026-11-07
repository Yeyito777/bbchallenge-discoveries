From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z278 XCuts.b278 XCuts.z279 XCuts.b279 XCuts.n278 XCuts.v278 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
