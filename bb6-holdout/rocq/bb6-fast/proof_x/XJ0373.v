From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z373 XCuts.b373 XCuts.z374 XCuts.b374 XCuts.n373 XCuts.v373 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
