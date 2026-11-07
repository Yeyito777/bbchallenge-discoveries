From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z239 XCuts.b239 XCuts.z240 XCuts.b240 XCuts.n239 XCuts.v239 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
