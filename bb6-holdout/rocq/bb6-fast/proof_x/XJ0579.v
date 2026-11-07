From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z579 XCuts.b579 XCuts.z580 XCuts.b580 XCuts.n579 XCuts.v579 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
