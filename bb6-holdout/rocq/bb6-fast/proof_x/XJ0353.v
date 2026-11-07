From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z353 XCuts.b353 XCuts.z354 XCuts.b354 XCuts.n353 XCuts.v353 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
