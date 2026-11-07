From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z57 XCuts.b57 XCuts.z58 XCuts.b58 XCuts.n57 XCuts.v57 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
