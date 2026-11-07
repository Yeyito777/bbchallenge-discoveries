From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z537 XCuts.b537 XCuts.z538 XCuts.b538 XCuts.n537 XCuts.v537 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
