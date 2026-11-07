From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z116 XCuts.b116 XCuts.z117 XCuts.b117 XCuts.n116 XCuts.v116 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
