From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z104 XCuts.b104 XCuts.z105 XCuts.b105 XCuts.n104 XCuts.v104 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
