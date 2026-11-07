From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z74 XCuts.b74 XCuts.z75 XCuts.b75 XCuts.n74 XCuts.v74 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
