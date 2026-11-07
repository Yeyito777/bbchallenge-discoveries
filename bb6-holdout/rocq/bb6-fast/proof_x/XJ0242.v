From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z242 XCuts.b242 XCuts.z243 XCuts.b243 XCuts.n242 XCuts.v242 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
