From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z44 XCuts.b44 XCuts.z45 XCuts.b45 XCuts.n44 XCuts.v44 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
