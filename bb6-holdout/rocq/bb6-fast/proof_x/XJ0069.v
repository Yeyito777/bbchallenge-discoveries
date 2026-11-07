From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z69 XCuts.b69 XCuts.z70 XCuts.b70 XCuts.n69 XCuts.v69 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
