From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z348 XCuts.b348 XCuts.z349 XCuts.b349 XCuts.n348 XCuts.v348 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
