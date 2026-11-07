From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z411 XCuts.b411 XCuts.z412 XCuts.b412 XCuts.n411 XCuts.v411 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
