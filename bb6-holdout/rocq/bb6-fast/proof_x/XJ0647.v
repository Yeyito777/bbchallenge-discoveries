From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z647 XCuts.b647 XCuts.z648 XCuts.b648 XCuts.n647 XCuts.v647 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
