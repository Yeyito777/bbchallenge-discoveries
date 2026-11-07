From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z531 XCuts.b531 XCuts.z532 XCuts.b532 XCuts.n531 XCuts.v531 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
