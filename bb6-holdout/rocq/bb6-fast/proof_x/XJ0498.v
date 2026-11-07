From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z498 XCuts.b498 XCuts.z499 XCuts.b499 XCuts.n498 XCuts.v498 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
