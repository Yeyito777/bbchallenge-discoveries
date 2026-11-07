From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z455 XCuts.b455 XCuts.z456 XCuts.b456 XCuts.n455 XCuts.v455 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
