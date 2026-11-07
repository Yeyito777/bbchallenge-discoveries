From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z38 XCuts.b38 XCuts.z39 XCuts.b39 XCuts.n38 XCuts.v38 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
