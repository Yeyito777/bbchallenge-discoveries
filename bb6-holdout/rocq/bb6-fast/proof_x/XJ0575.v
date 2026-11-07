From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z575 XCuts.b575 XCuts.z576 XCuts.b576 XCuts.n575 XCuts.v575 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
