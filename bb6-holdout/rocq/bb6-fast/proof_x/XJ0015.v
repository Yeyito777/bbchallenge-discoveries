From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z15 XCuts.b15 XCuts.z16 XCuts.b16 XCuts.n15 XCuts.v15 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
