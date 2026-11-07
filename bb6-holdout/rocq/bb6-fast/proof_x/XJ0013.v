From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z13 XCuts.b13 XCuts.z14 XCuts.b14 XCuts.n13 XCuts.v13 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
