From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z423 XCuts.b423 XCuts.z424 XCuts.b424 XCuts.n423 XCuts.v423 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
