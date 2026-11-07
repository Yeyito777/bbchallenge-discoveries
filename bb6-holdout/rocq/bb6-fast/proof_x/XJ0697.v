From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z697 XCuts.b697 XCuts.z698 XCuts.b698 XCuts.n697 XCuts.v697 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
