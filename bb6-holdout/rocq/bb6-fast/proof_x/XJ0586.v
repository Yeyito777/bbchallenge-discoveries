From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z586 XCuts.b586 XCuts.z587 XCuts.b587 XCuts.n586 XCuts.v586 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
