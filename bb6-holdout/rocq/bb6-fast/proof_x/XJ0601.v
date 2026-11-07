From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z601 XCuts.b601 XCuts.z602 XCuts.b602 XCuts.n601 XCuts.v601 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
