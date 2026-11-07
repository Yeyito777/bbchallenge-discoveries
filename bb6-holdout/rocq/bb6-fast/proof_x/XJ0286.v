From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z286 XCuts.b286 XCuts.z287 XCuts.b287 XCuts.n286 XCuts.v286 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
