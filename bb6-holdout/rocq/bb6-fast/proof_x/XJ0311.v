From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z311 XCuts.b311 XCuts.z312 XCuts.b312 XCuts.n311 XCuts.v311 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
