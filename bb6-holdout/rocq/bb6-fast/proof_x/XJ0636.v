From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z636 XCuts.b636 XCuts.z637 XCuts.b637 XCuts.n636 XCuts.v636 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
