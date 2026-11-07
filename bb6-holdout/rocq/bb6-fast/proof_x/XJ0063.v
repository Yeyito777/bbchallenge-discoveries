From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z63 XCuts.b63 XCuts.z64 XCuts.b64 XCuts.n63 XCuts.v63 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
