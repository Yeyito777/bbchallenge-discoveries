From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z96 XCuts.b96 XCuts.z97 XCuts.b97 XCuts.n96 XCuts.v96 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
