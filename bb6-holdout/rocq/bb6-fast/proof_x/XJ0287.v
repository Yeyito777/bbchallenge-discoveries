From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z287 XCuts.b287 XCuts.z288 XCuts.b288 XCuts.n287 XCuts.v287 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
