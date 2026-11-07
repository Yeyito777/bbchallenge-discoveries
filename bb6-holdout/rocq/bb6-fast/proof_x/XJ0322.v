From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z322 XCuts.b322 XCuts.z323 XCuts.b323 XCuts.n322 XCuts.v322 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
