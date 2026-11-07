From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z52 XCuts.b52 XCuts.z53 XCuts.b53 XCuts.n52 XCuts.v52 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
