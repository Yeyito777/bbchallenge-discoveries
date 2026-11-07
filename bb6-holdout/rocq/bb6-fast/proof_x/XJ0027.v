From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z27 XCuts.b27 XCuts.z28 XCuts.b28 XCuts.n27 XCuts.v27 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
