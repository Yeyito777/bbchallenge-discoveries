From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z34 XCuts.b34 XCuts.z35 XCuts.b35 XCuts.n34 XCuts.v34 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
