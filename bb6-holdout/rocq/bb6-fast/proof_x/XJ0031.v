From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z31 XCuts.b31 XCuts.z32 XCuts.b32 XCuts.n31 XCuts.v31 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
