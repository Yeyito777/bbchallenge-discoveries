From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z151 XCuts.b151 XCuts.z152 XCuts.b152 XCuts.n151 XCuts.v151 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
