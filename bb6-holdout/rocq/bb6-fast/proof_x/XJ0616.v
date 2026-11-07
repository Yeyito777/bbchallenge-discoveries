From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z616 XCuts.b616 XCuts.z617 XCuts.b617 XCuts.n616 XCuts.v616 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
