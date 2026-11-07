From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z138 XCuts.b138 XCuts.z139 XCuts.b139 XCuts.n138 XCuts.v138 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
