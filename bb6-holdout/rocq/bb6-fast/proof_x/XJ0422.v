From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z422 XCuts.b422 XCuts.z423 XCuts.b423 XCuts.n422 XCuts.v422 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
