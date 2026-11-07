From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z75 XCuts.b75 XCuts.z76 XCuts.b76 XCuts.n75 XCuts.v75 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
