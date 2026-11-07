From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z700 XCuts.b700 XCuts.z701 XCuts.b701 XCuts.n700 XCuts.v700 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
