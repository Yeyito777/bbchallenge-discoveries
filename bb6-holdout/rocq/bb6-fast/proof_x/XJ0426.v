From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z426 XCuts.b426 XCuts.z427 XCuts.b427 XCuts.n426 XCuts.v426 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
