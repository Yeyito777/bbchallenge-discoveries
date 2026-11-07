From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z546 XCuts.b546 XCuts.z547 XCuts.b547 XCuts.n546 XCuts.v546 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
