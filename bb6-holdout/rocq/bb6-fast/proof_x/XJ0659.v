From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z659 XCuts.b659 XCuts.z660 XCuts.b660 XCuts.n659 XCuts.v659 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
