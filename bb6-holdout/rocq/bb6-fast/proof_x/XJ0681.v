From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z681 XCuts.b681 XCuts.z682 XCuts.b682 XCuts.n681 XCuts.v681 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
