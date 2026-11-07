From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z61 XCuts.b61 XCuts.z62 XCuts.b62 XCuts.n61 XCuts.v61 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
