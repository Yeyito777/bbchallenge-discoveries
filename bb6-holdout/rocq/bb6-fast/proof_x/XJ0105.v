From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z105 XCuts.b105 XCuts.z106 XCuts.b106 XCuts.n105 XCuts.v105 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
