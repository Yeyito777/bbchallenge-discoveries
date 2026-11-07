From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z143 XCuts.b143 XCuts.z144 XCuts.b144 XCuts.n143 XCuts.v143 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
