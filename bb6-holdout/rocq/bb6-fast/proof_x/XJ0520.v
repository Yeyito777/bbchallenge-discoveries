From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z520 XCuts.b520 XCuts.z521 XCuts.b521 XCuts.n520 XCuts.v520 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
