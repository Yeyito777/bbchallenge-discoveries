From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z444 XCuts.b444 XCuts.z445 XCuts.b445 XCuts.n444 XCuts.v444 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
