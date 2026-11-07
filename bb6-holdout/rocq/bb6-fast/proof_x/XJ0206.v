From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z206 XCuts.b206 XCuts.z207 XCuts.b207 XCuts.n206 XCuts.v206 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
