From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z416 XCuts.b416 XCuts.z417 XCuts.b417 XCuts.n416 XCuts.v416 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
