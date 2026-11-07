From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z37 XCuts.b37 XCuts.z38 XCuts.b38 XCuts.n37 XCuts.v37 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
