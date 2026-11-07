From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z19 XCuts.b19 XCuts.z20 XCuts.b20 XCuts.n19 XCuts.v19 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
