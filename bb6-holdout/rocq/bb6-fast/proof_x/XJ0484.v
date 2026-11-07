From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z484 XCuts.b484 XCuts.z485 XCuts.b485 XCuts.n484 XCuts.v484 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
