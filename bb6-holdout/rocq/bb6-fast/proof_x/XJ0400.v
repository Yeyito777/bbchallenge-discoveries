From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z400 XCuts.b400 XCuts.z401 XCuts.b401 XCuts.n400 XCuts.v400 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
