From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z329 XCuts.b329 XCuts.z330 XCuts.b330 XCuts.n329 XCuts.v329 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
