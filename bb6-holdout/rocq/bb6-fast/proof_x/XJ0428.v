From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z428 XCuts.b428 XCuts.z429 XCuts.b429 XCuts.n428 XCuts.v428 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
