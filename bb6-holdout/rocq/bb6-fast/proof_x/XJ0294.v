From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z294 XCuts.b294 XCuts.z295 XCuts.b295 XCuts.n294 XCuts.v294 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
