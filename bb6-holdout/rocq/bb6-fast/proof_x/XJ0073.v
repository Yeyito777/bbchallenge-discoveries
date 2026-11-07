From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z73 XCuts.b73 XCuts.z74 XCuts.b74 XCuts.n73 XCuts.v73 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
