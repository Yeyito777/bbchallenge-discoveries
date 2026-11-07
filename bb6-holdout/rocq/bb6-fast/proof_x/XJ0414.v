From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z414 XCuts.b414 XCuts.z415 XCuts.b415 XCuts.n414 XCuts.v414 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
