From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z316 XCuts.b316 XCuts.z317 XCuts.b317 XCuts.n316 XCuts.v316 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
