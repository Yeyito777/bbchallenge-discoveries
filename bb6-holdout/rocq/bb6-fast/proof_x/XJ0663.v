From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z663 XCuts.b663 XCuts.z664 XCuts.b664 XCuts.n663 XCuts.v663 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
