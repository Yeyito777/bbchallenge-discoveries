From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z98 XCuts.b98 XCuts.z99 XCuts.b99 XCuts.n98 XCuts.v98 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
