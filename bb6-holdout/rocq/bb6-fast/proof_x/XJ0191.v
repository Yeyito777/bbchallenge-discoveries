From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z191 XCuts.b191 XCuts.z192 XCuts.b192 XCuts.n191 XCuts.v191 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
