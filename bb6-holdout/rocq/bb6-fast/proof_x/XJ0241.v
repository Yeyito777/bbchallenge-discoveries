From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z241 XCuts.b241 XCuts.z242 XCuts.b242 XCuts.n241 XCuts.v241 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
