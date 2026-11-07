From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z270 XCuts.b270 XCuts.z271 XCuts.b271 XCuts.n270 XCuts.v270 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
