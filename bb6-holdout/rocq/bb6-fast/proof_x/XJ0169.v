From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z169 XCuts.b169 XCuts.z170 XCuts.b170 XCuts.n169 XCuts.v169 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
