From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z686 XCuts.b686 XCuts.z687 XCuts.b687 XCuts.n686 XCuts.v686 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
