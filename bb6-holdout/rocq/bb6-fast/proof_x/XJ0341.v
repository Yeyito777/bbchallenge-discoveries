From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z341 XCuts.b341 XCuts.z342 XCuts.b342 XCuts.n341 XCuts.v341 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
