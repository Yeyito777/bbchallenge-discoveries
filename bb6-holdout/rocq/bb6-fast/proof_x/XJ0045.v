From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z45 XCuts.b45 XCuts.z46 XCuts.b46 XCuts.n45 XCuts.v45 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
