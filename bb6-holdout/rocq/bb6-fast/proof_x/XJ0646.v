From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z646 XCuts.b646 XCuts.z647 XCuts.b647 XCuts.n646 XCuts.v646 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
