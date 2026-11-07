From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z433 XCuts.b433 XCuts.z434 XCuts.b434 XCuts.n433 XCuts.v433 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
