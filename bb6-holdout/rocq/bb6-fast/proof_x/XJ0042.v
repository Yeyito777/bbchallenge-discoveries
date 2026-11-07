From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z42 XCuts.b42 XCuts.z43 XCuts.b43 XCuts.n42 XCuts.v42 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
