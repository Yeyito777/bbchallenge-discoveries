From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z93 XCuts.b93 XCuts.z94 XCuts.b94 XCuts.n93 XCuts.v93 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
