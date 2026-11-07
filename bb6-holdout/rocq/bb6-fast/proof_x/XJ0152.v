From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z152 XCuts.b152 XCuts.z153 XCuts.b153 XCuts.n152 XCuts.v152 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
