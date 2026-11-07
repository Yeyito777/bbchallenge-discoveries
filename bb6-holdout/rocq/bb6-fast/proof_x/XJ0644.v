From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z644 XCuts.b644 XCuts.z645 XCuts.b645 XCuts.n644 XCuts.v644 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
