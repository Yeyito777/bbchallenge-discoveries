From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z32 XCuts.b32 XCuts.z33 XCuts.b33 XCuts.n32 XCuts.v32 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
