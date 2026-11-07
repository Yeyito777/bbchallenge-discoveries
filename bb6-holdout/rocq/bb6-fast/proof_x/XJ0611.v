From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z611 XCuts.b611 XCuts.z612 XCuts.b612 XCuts.n611 XCuts.v611 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
