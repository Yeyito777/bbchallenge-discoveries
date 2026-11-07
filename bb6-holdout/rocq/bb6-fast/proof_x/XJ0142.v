From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z142 XCuts.b142 XCuts.z143 XCuts.b143 XCuts.n142 XCuts.v142 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
