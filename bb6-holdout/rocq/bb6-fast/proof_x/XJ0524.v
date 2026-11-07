From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z524 XCuts.b524 XCuts.z525 XCuts.b525 XCuts.n524 XCuts.v524 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
