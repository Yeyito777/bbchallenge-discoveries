From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z490 XCuts.b490 XCuts.z491 XCuts.b491 XCuts.n490 XCuts.v490 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
