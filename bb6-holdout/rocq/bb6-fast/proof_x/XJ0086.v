From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z86 XCuts.b86 XCuts.z87 XCuts.b87 XCuts.n86 XCuts.v86 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
