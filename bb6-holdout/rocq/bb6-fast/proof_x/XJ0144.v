From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z144 XCuts.b144 XCuts.z145 XCuts.b145 XCuts.n144 XCuts.v144 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
