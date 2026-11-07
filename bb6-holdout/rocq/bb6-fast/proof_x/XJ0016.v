From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z16 XCuts.b16 XCuts.z17 XCuts.b17 XCuts.n16 XCuts.v16 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
