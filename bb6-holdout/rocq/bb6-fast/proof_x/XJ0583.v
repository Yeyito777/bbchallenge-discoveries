From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z583 XCuts.b583 XCuts.z584 XCuts.b584 XCuts.n583 XCuts.v583 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
