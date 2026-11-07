From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z395 XCuts.b395 XCuts.z396 XCuts.b396 XCuts.n395 XCuts.v395 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
