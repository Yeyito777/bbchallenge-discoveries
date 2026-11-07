From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z436 XCuts.b436 XCuts.z437 XCuts.b437 XCuts.n436 XCuts.v436 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
