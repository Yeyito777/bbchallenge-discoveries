From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z275 XCuts.b275 XCuts.z276 XCuts.b276 XCuts.n275 XCuts.v275 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
