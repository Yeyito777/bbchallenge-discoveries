From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z296 XCuts.b296 XCuts.z297 XCuts.b297 XCuts.n296 XCuts.v296 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
