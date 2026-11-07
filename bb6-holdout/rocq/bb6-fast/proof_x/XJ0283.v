From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z283 XCuts.b283 XCuts.z284 XCuts.b284 XCuts.n283 XCuts.v283 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
