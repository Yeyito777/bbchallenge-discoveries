From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z534 XCuts.b534 XCuts.z535 XCuts.b535 XCuts.n534 XCuts.v534 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
