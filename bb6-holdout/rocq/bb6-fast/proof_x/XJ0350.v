From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z350 XCuts.b350 XCuts.z351 XCuts.b351 XCuts.n350 XCuts.v350 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
