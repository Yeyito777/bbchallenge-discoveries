From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z90 XCuts.b90 XCuts.z91 XCuts.b91 XCuts.n90 XCuts.v90 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
