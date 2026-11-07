From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z33 XCuts.b33 XCuts.z34 XCuts.b34 XCuts.n33 XCuts.v33 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
