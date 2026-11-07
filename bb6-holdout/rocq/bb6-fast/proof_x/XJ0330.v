From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z330 XCuts.b330 XCuts.z331 XCuts.b331 XCuts.n330 XCuts.v330 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
