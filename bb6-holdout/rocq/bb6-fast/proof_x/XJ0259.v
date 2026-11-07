From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z259 XCuts.b259 XCuts.z260 XCuts.b260 XCuts.n259 XCuts.v259 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
