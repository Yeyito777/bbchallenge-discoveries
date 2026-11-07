From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z24 XCuts.b24 XCuts.z25 XCuts.b25 XCuts.n24 XCuts.v24 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
