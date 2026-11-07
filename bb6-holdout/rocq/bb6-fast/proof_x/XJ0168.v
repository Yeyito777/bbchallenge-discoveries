From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z168 XCuts.b168 XCuts.z169 XCuts.b169 XCuts.n168 XCuts.v168 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
