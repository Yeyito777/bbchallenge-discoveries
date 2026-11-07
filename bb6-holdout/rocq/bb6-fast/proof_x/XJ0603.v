From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z603 XCuts.b603 XCuts.z604 XCuts.b604 XCuts.n603 XCuts.v603 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
