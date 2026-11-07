From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z41 XCuts.b41 XCuts.z42 XCuts.b42 XCuts.n41 XCuts.v41 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
