From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z451 XCuts.b451 XCuts.z452 XCuts.b452 XCuts.n451 XCuts.v451 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
