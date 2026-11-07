From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z190 XCuts.b190 XCuts.z191 XCuts.b191 XCuts.n190 XCuts.v190 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
