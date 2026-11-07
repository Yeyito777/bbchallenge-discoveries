From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z185 XCuts.b185 XCuts.z186 XCuts.b186 XCuts.n185 XCuts.v185 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
