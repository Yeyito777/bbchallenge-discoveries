From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z515 XCuts.b515 XCuts.z516 XCuts.b516 XCuts.n515 XCuts.v515 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
