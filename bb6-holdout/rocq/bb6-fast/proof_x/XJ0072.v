From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z72 XCuts.b72 XCuts.z73 XCuts.b73 XCuts.n72 XCuts.v72 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
