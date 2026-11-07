From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z465 XCuts.b465 XCuts.z466 XCuts.b466 XCuts.n465 XCuts.v465 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
