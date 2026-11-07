From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z132 XCuts.b132 XCuts.z133 XCuts.b133 XCuts.n132 XCuts.v132 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
