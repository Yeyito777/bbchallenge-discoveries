From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z141 XCuts.b141 XCuts.z142 XCuts.b142 XCuts.n141 XCuts.v141 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
