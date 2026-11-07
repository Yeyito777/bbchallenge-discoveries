From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z88 XCuts.b88 XCuts.z89 XCuts.b89 XCuts.n88 XCuts.v88 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
