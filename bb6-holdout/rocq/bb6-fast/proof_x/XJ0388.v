From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z388 XCuts.b388 XCuts.z389 XCuts.b389 XCuts.n388 XCuts.v388 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
