From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z421 XCuts.b421 XCuts.z422 XCuts.b422 XCuts.n421 XCuts.v421 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
