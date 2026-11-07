From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z339 XCuts.b339 XCuts.z340 XCuts.b340 XCuts.n339 XCuts.v339 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
