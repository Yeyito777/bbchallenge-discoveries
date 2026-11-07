From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z435 XCuts.b435 XCuts.z436 XCuts.b436 XCuts.n435 XCuts.v435 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
