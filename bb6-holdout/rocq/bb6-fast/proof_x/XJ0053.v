From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z53 XCuts.b53 XCuts.z54 XCuts.b54 XCuts.n53 XCuts.v53 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
