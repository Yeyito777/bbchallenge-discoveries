From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z240 XCuts.b240 XCuts.z241 XCuts.b241 XCuts.n240 XCuts.v240 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
