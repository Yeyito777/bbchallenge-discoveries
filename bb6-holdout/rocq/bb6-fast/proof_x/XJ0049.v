From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z49 XCuts.b49 XCuts.z50 XCuts.b50 XCuts.n49 XCuts.v49 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
