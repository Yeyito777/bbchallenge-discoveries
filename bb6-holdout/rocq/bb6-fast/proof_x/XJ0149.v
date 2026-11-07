From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z149 XCuts.b149 XCuts.z150 XCuts.b150 XCuts.n149 XCuts.v149 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
