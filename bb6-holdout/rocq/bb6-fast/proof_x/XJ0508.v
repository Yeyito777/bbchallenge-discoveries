From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z508 XCuts.b508 XCuts.z509 XCuts.b509 XCuts.n508 XCuts.v508 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
