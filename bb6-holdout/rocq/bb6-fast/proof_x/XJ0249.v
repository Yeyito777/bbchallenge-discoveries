From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z249 XCuts.b249 XCuts.z250 XCuts.b250 XCuts.n249 XCuts.v249 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
