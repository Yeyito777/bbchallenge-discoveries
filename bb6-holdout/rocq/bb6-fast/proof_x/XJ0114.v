From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z114 XCuts.b114 XCuts.z115 XCuts.b115 XCuts.n114 XCuts.v114 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
