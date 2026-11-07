From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z391 XCuts.b391 XCuts.z392 XCuts.b392 XCuts.n391 XCuts.v391 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
