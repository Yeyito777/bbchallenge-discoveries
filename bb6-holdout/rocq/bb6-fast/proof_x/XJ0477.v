From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z477 XCuts.b477 XCuts.z478 XCuts.b478 XCuts.n477 XCuts.v477 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
