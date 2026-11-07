From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z432 XCuts.b432 XCuts.z433 XCuts.b433 XCuts.n432 XCuts.v432 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
