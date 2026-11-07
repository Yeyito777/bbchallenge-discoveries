From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z377 XCuts.b377 XCuts.z378 XCuts.b378 XCuts.n377 XCuts.v377 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
