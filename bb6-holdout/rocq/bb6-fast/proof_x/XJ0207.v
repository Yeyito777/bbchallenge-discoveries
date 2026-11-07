From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z207 XCuts.b207 XCuts.z208 XCuts.b208 XCuts.n207 XCuts.v207 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
