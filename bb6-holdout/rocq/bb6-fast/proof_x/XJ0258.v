From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z258 XCuts.b258 XCuts.z259 XCuts.b259 XCuts.n258 XCuts.v258 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
