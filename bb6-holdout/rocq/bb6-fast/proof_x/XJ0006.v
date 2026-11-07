From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z6 XCuts.b6 XCuts.z7 XCuts.b7 XCuts.n6 XCuts.v6 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
