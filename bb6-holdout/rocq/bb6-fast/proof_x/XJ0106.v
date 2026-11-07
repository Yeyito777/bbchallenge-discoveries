From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z106 XCuts.b106 XCuts.z107 XCuts.b107 XCuts.n106 XCuts.v106 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
