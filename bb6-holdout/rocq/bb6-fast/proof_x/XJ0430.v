From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z430 XCuts.b430 XCuts.z431 XCuts.b431 XCuts.n430 XCuts.v430 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
