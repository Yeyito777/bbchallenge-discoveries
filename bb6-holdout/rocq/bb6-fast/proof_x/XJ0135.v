From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z135 XCuts.b135 XCuts.z136 XCuts.b136 XCuts.n135 XCuts.v135 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
