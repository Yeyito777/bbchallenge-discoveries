From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z512 XCuts.b512 XCuts.z513 XCuts.b513 XCuts.n512 XCuts.v512 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
