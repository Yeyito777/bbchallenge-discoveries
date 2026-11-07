From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z445 XCuts.b445 XCuts.z446 XCuts.b446 XCuts.n445 XCuts.v445 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
