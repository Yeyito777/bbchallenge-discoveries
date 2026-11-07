From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z199 XCuts.b199 XCuts.z200 XCuts.b200 XCuts.n199 XCuts.v199 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
