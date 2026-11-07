From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z363 XCuts.b363 XCuts.z364 XCuts.b364 XCuts.n363 XCuts.v363 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
