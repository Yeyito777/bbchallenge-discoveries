From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z39 XCuts.b39 XCuts.z40 XCuts.b40 XCuts.n39 XCuts.v39 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
