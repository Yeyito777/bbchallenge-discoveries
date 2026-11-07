From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z71 XCuts.b71 XCuts.z72 XCuts.b72 XCuts.n71 XCuts.v71 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
