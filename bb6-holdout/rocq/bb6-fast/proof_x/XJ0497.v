From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z497 XCuts.b497 XCuts.z498 XCuts.b498 XCuts.n497 XCuts.v497 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
