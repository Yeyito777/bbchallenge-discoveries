From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z282 XCuts.b282 XCuts.z283 XCuts.b283 XCuts.n282 XCuts.v282 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
