From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z393 XCuts.b393 XCuts.z394 XCuts.b394 XCuts.n393 XCuts.v393 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
