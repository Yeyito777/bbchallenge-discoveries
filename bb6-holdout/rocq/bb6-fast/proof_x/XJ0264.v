From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z264 XCuts.b264 XCuts.z265 XCuts.b265 XCuts.n264 XCuts.v264 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
