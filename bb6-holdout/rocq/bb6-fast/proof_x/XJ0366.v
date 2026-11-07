From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z366 XCuts.b366 XCuts.z367 XCuts.b367 XCuts.n366 XCuts.v366 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
