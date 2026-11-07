From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z107 XCuts.b107 XCuts.z108 XCuts.b108 XCuts.n107 XCuts.v107 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
