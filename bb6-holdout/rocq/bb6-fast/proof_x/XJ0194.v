From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z194 XCuts.b194 XCuts.z195 XCuts.b195 XCuts.n194 XCuts.v194 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
