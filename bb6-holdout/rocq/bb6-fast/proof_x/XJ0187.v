From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z187 XCuts.b187 XCuts.z188 XCuts.b188 XCuts.n187 XCuts.v187 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
