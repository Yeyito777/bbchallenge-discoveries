From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z584 XCuts.b584 XCuts.z585 XCuts.b585 XCuts.n584 XCuts.v584 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
