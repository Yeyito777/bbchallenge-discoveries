From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z605 XCuts.b605 XCuts.z606 XCuts.b606 XCuts.n605 XCuts.v605 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
