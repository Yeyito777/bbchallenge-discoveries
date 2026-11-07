From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z26 XCuts.b26 XCuts.z27 XCuts.b27 XCuts.n26 XCuts.v26 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
