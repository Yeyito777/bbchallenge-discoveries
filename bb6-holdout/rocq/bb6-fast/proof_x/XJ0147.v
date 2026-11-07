From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z147 XCuts.b147 XCuts.z148 XCuts.b148 XCuts.n147 XCuts.v147 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
