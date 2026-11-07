From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z184 XCuts.b184 XCuts.z185 XCuts.b185 XCuts.n184 XCuts.v184 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
