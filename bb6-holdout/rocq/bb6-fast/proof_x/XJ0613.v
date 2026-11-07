From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z613 XCuts.b613 XCuts.z614 XCuts.b614 XCuts.n613 XCuts.v613 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
