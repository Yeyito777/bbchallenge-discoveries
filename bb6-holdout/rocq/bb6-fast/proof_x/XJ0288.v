From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z288 XCuts.b288 XCuts.z289 XCuts.b289 XCuts.n288 XCuts.v288 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
