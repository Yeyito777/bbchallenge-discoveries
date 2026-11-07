From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z97 XCuts.b97 XCuts.z98 XCuts.b98 XCuts.n97 XCuts.v97 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
