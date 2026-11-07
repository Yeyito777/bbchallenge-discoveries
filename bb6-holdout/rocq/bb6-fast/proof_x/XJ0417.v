From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z417 XCuts.b417 XCuts.z418 XCuts.b418 XCuts.n417 XCuts.v417 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
