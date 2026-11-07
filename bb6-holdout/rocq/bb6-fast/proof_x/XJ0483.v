From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z483 XCuts.b483 XCuts.z484 XCuts.b484 XCuts.n483 XCuts.v483 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
