From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z28 XCuts.b28 XCuts.z29 XCuts.b29 XCuts.n28 XCuts.v28 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
