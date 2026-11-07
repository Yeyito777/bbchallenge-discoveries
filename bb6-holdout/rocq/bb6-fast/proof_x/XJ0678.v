From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z678 XCuts.b678 XCuts.z679 XCuts.b679 XCuts.n678 XCuts.v678 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
