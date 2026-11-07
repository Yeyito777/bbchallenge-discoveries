From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z82 XCuts.b82 XCuts.z83 XCuts.b83 XCuts.n82 XCuts.v82 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
