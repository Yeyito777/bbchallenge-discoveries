From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z491 XCuts.b491 XCuts.z492 XCuts.b492 XCuts.n491 XCuts.v491 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
