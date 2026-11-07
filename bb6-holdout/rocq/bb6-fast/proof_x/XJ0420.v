From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z420 XCuts.b420 XCuts.z421 XCuts.b421 XCuts.n420 XCuts.v420 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
