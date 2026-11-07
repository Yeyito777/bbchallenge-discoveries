From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z29 XCuts.b29 XCuts.z30 XCuts.b30 XCuts.n29 XCuts.v29 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
