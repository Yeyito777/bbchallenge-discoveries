From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z279 XCuts.b279 XCuts.z280 XCuts.b280 XCuts.n279 XCuts.v279 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
