From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z450 XCuts.b450 XCuts.z451 XCuts.b451 XCuts.n450 XCuts.v450 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
