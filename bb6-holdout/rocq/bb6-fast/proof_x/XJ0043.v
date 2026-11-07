From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z43 XCuts.b43 XCuts.z44 XCuts.b44 XCuts.n43 XCuts.v43 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
